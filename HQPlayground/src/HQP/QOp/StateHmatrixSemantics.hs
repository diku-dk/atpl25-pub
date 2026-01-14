module HQP.QOp.StateHmatrixSemantics
 {-| ( StateT
  , OpT(..)
  , apply
  , evalOp      -- :: QOp -> OpT
  , evalStep    -- :: (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
  , evalProg    -- :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG)
  , measure1    -- :: (StateT, Outcomes, RNG) -> Int -> (StateT, Outcomes, RNG)
  , applyPauliProduct
  , ket
  , onLeftBlock
  , onRightBlock
  , view
  , evalOpMat
  ) where
-}
where

import Data.Complex

import HQP.QOp.Syntax          
import HQP.QOp.HelperFunctions
import HQP.PrettyPrint.PrettyOp
import HQP.QOp.MatrixSemantics(CMat,CMatable(..))
import qualified HQP.PrettyPrint.PrettyMatrix as PS
import Data.Bits(shiftL,xor,testBit, setBit, clearBit)
import Data.Array(accumArray,elems)
--import qualified Torch as T
--import qualified Torch.Functional as F
--import qualified Torch.Tensor as TT
import Data.Bits (testBit, setBit)
import Data.List (foldl')
import Data.Complex (Complex, conjugate)
import Numeric.LinearAlgebra
  ( Matrix, (><), reshape, flatten, toList, atIndex
  , fromBlocks, fromRows, toRows,subMatrix, cmap, cols, rows, scale, sumElements
  )

import qualified Numeric.LinearAlgebra as HMat
import qualified Foreign.Storable as FFI
type StateT   = CMat
type WorkT    = CMat
--type WorkT = StateT

{-# INLINE index2 #-}
{-# INLINE make2 #-}
{-# INLINE view2 #-}
{-# INLINE splitFront #-}
{-# INLINE stackFront #-}
{-# INLINE backpermute2 #-}
tol = 1e-12

-- | Backend API
-- | makeArray-like builder and element lookup
class HasWork t where
  toWork   :: t -> WorkT
  fromWork :: WorkT -> t

instance HasWork WorkT where
  toWork   = id
  fromWork = id

make2  :: (Int,Int) -> ((Int,Int) -> ComplexT) -> WorkT
index2 :: WorkT -> (Int,Int) -> ComplexT

-- | view (reshape)
view2        :: (Int,Int) -> WorkT -> WorkT
splitFront   :: Int -> Int -> WorkT -> (WorkT,WorkT)
stackFront   :: Int -> Int -> WorkT -> WorkT -> WorkT
backpermute2 :: 
                (Int,Int)                -- (m,n), the shape of the array
             -> ((Int,Int) -> (Int,Int)) -- f: output index -> input index
             -> WorkT -> WorkT



-- | Transformer primitives
mapW :: (ComplexT -> ComplexT) -> WorkT -> WorkT
zipW :: (ComplexT -> ComplexT -> ComplexT) -> WorkT -> WorkT -> WorkT

--------------------------------------------------------------------------------
-- Backend-wide conventions
--------------------------------------------------------------------------------
type OpT = StateT -> StateT
type OpW = WorkT -> WorkT
--newtype OpT = OpT { runOpT :: StateT -> StateT }
--newtype OpW = OpW { runOpW :: WorkT -> WorkT   }

evalOp   :: QOp -> OpT
evalStep :: (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
evalProg :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG) 

apply :: OpT -> StateT -> StateT
apply f psi = f psi



--- BACKEND-SPECIFIC IMPLEMENTATION HERE - MOVE TO BACKEND FILE LATER ---

{-# LANGUAGE TupleSections #-}

singleKet v' = let v = fromIntegral v' :+ 0
               in  (2><1) [1-v,v] 

ket :: [Int] -> StateT
ket vs = foldr (⊗) ((1><1) [1]) (map singleKet vs)
  
--------------------------------------------------------------------------------
-- make/index
--------------------------------------------------------------------------------

-- | Build an (m×n) matrix by an element function f(i,j) with i,j zero-based.
make2 (m,n) f = (m >< n) [ f (i,j) | i <- [0..m-1], j <- [0..n-1] ]

-- | Zero-based indexing.
index2 a (i,j) = a `atIndex` (i,j)

--------------------------------------------------------------------------------
-- view / split / stack
--------------------------------------------------------------------------------

-- | Reshape (preserving linear order: row-major) to (m×n).
--   Precondition: m*n == rows(a)*cols(a).
view2 (m,n) a = reshape n (flatten a)  -- reshape takes columns count

{-|
permuteLocal :: [Int] -> Int -> Int -> WorkT -> WorkT
permuteLocal ks p _r psi =
  let n   = pow2 p
      s   = permSupport ks
      inv = invPerm ks
      bitPos i = p - 1 - i

      preimageRow y =
        foldl
          (\x i ->
             let src = inv !! i
                 b   = testBit y (bitPos src)
             in if b then setBit x (bitPos i) else clearBit x (bitPos i))
          y
          s

      rs = toRows psi
  in fromRows [ rs !! preimageRow y | y <- [0..n-1] ]
-}
permuteLocal :: [Int] -> Int -> Int -> Matrix ComplexT -> Matrix ComplexT
permuteLocal ks p r psi =
  let n      = pow2 p
      inv    = invertPerm ks
      bitPos i = p - 1 - i

      preimageRow y =
        let get i = testBit y (bitPos (inv !! i))
            put acc i = if get i then setBit acc (bitPos i) else clearBit acc (bitPos i)
        in foldl put 0 [0..p-1]

      -- rows of output: out[y,*] = in[preimageRow y,*]
      inRows = toRows psi
      outRows = [ inRows !! preimageRow y | y <- [0..n-1] ]
  in fromRows outRows


-- | Split along the front selector bit:
--   expects a shaped as (2^(k+1) × r), returns two (2^k × r) blocks:
--     a0 = rows [0..2^k-1], a1 = rows [2^k..2^(k+1)-1].
splitFront k r a =
  let m = 2^k
      a' = view2 (2*m, r) a
      a0 = subMatrix (0,0) (m,r) a'
      a1 = subMatrix (m,0) (m,r) a'
  in (a0,a1)

-- | Stack two (2^k × r) blocks into (2^(k+1) × r) by vertical concatenation.
stackFront k r a0 a1 =
  let m = 2^k
      b0 = view2 (m,r) a0
      b1 = view2 (m,r) a1
  in fromBlocks [[b0],[b1]]


-- | Direct-sum / controlled selector action:
--   ψ ↦ |0⟩⊗f0(ψ0) + |1⟩⊗f1(ψ1), where (ψ0,ψ1)=splitFront.
onSelector f0 f1 k r ψ =
  let (ψ0,ψ1) = splitFront k r ψ
  in stackFront k r (f0 ψ0) (f1 ψ1)

--------------------------------------------------------------------------------
-- 1-qubit atoms on the frontmost qubit 
--------------------------------------------------------------------------------
-- Each of these acts on Ψ : ℂ^{2^k × r} by viewing Ψ as ℂ^{2 × 2^(k-1) × r}
-- (front qubit axis explicit), applying the 2×2 rule along that axis, and 
-- restoring the original view.
applyX1, applyY1, applyZ1, applyH1, applySX1
  :: Int -> Int -> WorkT -> WorkT

{-| applyX1 implements (X ⊗ Id (k-1)) on k qubits.
    Action on basis: X|0⟩ = |1⟩,  X|1⟩ = |0⟩
    so it swaps the two slices of the front axis:
    Ψ'_{0,j,β} = Ψ_{1,j,β},  Ψ'_{1,j,β} = Ψ_{0,j,β}. -}
applyX1 k r psi =
  let n = pow2 k
      m = pow2 (k-1)
      a = view2 (n,r) psi
  in make2 (n,r) $ \(i,j) ->
       if i < m then index2 a (i+m, j)
                else index2 a (i-m, j)

{-| applyZ1 implements (Z ⊗ Id (k-1)) on k qubits.
    Action on basis:  Z|0⟩ = |0⟩,  Z|1⟩ = -|1⟩
    hence:  Ψ'_{0,j,β} = Ψ_{0,j,β},  Ψ'_{1,j,β} = -Ψ_{1,j,β}. -}
applyZ1 k r psi =
  let n = pow2 k
      m = pow2 (k-1)
      a = view2 (n,r) psi
  in make2 (n,r) $ \(i,j) ->
       let s = if i < m then 1:+0 else (-1):+0
       in s * index2 a (i,j)

{-| applyY1 implements (Y ⊗ Id (k-1)) on k qubits.
   Action on basis:
     Y|0⟩ =  i|1⟩,   Y|1⟩ = -i|0⟩
   hence:
     Ψ'_{0,j,β} = -i Ψ_{1,j,β}
     Ψ'_{1,j,β} =  i Ψ_{0,j,β}. -}
applyY1 k r psi =
  let n  = pow2 k
      m  = pow2 (k-1)
      a  = view2 (n,r) psi
      iC = 0:+1
      mi = 0:+(-1)
  in make2 (n,r) $ \(i,j) ->
       if i < m then mi * index2 a (i+m, j)   -- |0> <- -i |1>
                else iC * index2 a (i-m, j)   -- |1> <-  i |0>

{-| applyH1 implements (H ⊗ Id (k-1)) on k qubits.
   Action on basis:
     H|0⟩ = (|0⟩+|1⟩)/√2
     H|1⟩ = (|0⟩-|1⟩)/√2
   hence:
     Ψ'_{0,j,β} = 1/√2*(Ψ_{0,j,β} + Ψ_{1,j,β})
     Ψ'_{1,j,β} = 1/√2*(Ψ_{0,j,β} - Ψ_{1,j,β}) -}
applyH1 k r psi =
  let m = pow2 (k-1)         -- k qubits -> m = 2^(k-1) indices per half
      a = view2 (2*m,r) psi  -- Apply to first k qubits
      s = (1 / sqrt 2) :+ 0
  in make2 (2*m,r) $ \(i,j) ->
      let i0 = if i < m then i else i-m
          a0 = index2 a (i0,   j) -- |0> component of first qubit
          a1 = index2 a (i0+m, j) -- |1> component of first qubit
      in if i < m then 
        s*(a0 + a1)  -- H|0⟩ = (|0⟩+|1⟩)/√2
      else 
        s*(a0 - a1)  -- H|1⟩ = (|0⟩-|1⟩)/√2

{-| applySX1 implements (SX ⊗ Id (k-1)) on k qubits.
   Action on basis:
     SX|0⟩ = ( (1+i)|0> + (1-i)|1> ) /2
     SX|1⟩ = ( (1-i)|0> + (1+i)|1> ) /2
-}
applySX1 k r psi =
  let
      m  = pow2 (k-1)
      a  = view2 (2*m,r) psi
      h  = 0.5 :+ 0
      (p,q)  = (1:+1, 1:+(-1))  -- (1+i), (1-i)
  in make2 (2*m,r) $ \(i,j) ->
      let i0 = if i < m then i else i - m
          a0 = index2 a (i0,   j)
          a1 = index2 a (i0+m, j)
      in if i < m then 
          h * (p*a0 + q*a1)
      else 
          h * (q*a0 + p*a1)



-- | backpermute2 (m,n) f a constructs out of shape (m×n):
--     out(i,j) = a(f(i,j)).
--   Indices are zero-based.
backpermute2 (m,n) f a =
  make2 (m,n) $ \(i,j) ->
    let (i',j') = f (i,j)
    in index2 a (i',j')

--------------------------------------------------------------------------------
-- map/zip/dot
--------------------------------------------------------------------------------

mapW = cmap

zipW f a b =
  let (m,n) = (rows a, cols a)
  in make2 (m,n) $ \(i,j) -> f (index2 a (i,j)) (index2 b (i,j))

-- | dotC ⟨a|b⟩ = Σ conj(a_ij) * b_ij  (shape must match).
dotC a b =
  let xs = toList (flatten a)
      ys = toList (flatten b)
  in sum (zipWith (\x y -> conjugate x * y) xs ys)


onLeftBlock kA kB r f psi = 
  let psiL = view2 ((pow2 kA), (pow2 kB) * r) psi
  in  view2 (pow2 (kA+kB), r) (f psiL)

{-|onRightBlock kA kB r opB applies opB = [[B]] to the right block of a state tensor, i.e.:

    Ψ ↦ [[(Id kA) ⊗ B Ψ]] 

  analogously to onLeftBlock.
-}
onRightBlock
  ::
     Int -> Int -> Int                             -- kA kB r
  -> (WorkT -> WorkT)                              -- B-op on [2^kB, 2^kA*r]
  -> WorkT                                         -- psi on [2^(kA+kB), r]
  -> WorkT                                         -- output on [2^(kA+kB), r]
onRightBlock kA kB r bop = \psi ->
  let a  = pow2 kA
      b  = pow2 kB
      ab = a*b

      -- x  = aIdx*b + bIdx
      -- x' = bIdx*a + aIdx

      swapRow x   = let (q,ra) = x `divMod` a in ra*b + q      -- (bIdx,aIdx)->(aIdx,bIdx)
      unswapRow x = let (q,rb) = x `divMod` b in rb*a + q      -- (aIdx,bIdx)->(bIdx,aIdx)

      -- IMPORTANT: backpermute uses output -> input.
      toSwapped   (x,j) = (swapRow   x, j)  -- out(x)=in(unswap x) gives ψS[x'] = ψ[x]
      fromSwapped (x,j) = (unswapRow x, j)  -- inverse

      psi0  = view2 (ab, r) psi
      psiS  = backpermute2 (ab, r) toSwapped psi0
      psiSM = view2 (b, a*r) psiS
      outSM = bop psiSM
      outS  = view2 (ab, r) outSM
  in  backpermute2 (ab, r) fromSwapped outS


--------------------------------------------------------------------------------
-- Fast application of Pauli-product (as OpT + phase)
--------------------------------------------------------------------------------

-- Apply a Pauli product P (up to global phase) to a matrix-view Psi:[pow2 k,r].
-- Returns (globalPhase, opT) where endomorphism is the actual action on Psi.
--
-- Allowed constructors for P:
--   Id, Phase, X,Y,Z, Permute, Tensor, Compose, Adjoint
-- (No H, no DirectSum/C, no R).
pauliOp :: QOp -- Pauli product
        -> Int -- k   -- number of qubits acted on
        -> Int -- r   -- batch dimension
        -> (Complex Double, OpW) -- (global phase, operator on [pow2 k,r])
pauliOp op k r = go op
  where
    go = \case
      Id _       -> (1:+0,    id)
      Phase q    -> (exp(0:+ (pi * fromRational q)), id)

      X          -> (1:+0, applyX1 k r)
      Y          -> (1:+0, applyY1 k r)
      Z          -> (1:+0, applyZ1 k r)

      Permute ks -> (1:+0, permuteLocal ks k r)

      Compose a b ->
        let (ϕA, opA) = go a
            (ϕB, opB) = go b
        in (ϕA * ϕB, opA . opB)

      Tensor a b ->
        let kA = op_qubits a
            kB = op_qubits b
            (ϕA, fA) = pauliOp a kA (pow2 kB * r)
            (ϕB, fB) = pauliOp b kB (pow2 kA * r)
            fAxI = onLeftBlock  kA kB r fA
            fIxB = onRightBlock kA kB r fB
        in (ϕA * ϕB, (fIxB . fAxI))

      Adjoint a ->
        -- X,Y,Z,H are Hermitian; permutation inverts; Phase negates.
        go (dagger a)

      _ ->
        error "pauliEndo: non-Pauli constructor encountered"

-- apply a Pauli string with phase op=[[ϕ⋅P]] to a concrete Ψ, returning (ϕ, [[PΨ]])).
applyPauliProduct :: QOp -> Int -> Int -> WorkT -> (Complex Double, WorkT)
applyPauliProduct op k r ψ =
  let (ϕ, fP) = pauliOp op k r
  in  (ϕ, fP ψ)

--------------------------------------------------------------------------------
-- QOp semantics on matrix-views Psi:[pow2 k,r]
--------------------------------------------------------------------------------

-- Internal: matrix-view semantics, closes over (k,r).
{-| evalOpMat op k r applies the operator op to a state tensor viewed as [pow2 k, r],
    returning an OpT representing the action on that view.

    Note: this function assumes that op is well-typed for k qubits, i.e. op_qubits op == k.
-}
evalOpMat :: QOp -> Int -> Int -> OpW 
evalOpMat op k r = go op
  where
    go = \case
      Id _       -> id
      Phase q    -> (exp( 0:+ (pi * fromRational q)) .* )

      X          -> applyX1 k r
      Y          -> applyY1 k r
      Z          -> applyZ1 k r
      H          -> applyH1 k r
      SX         -> applySX1 k r
      Permute ks -> permuteLocal ks k r

      Compose a b -> go a . go b
      Adjoint a   -> go (dagger a)

      Tensor a b  ->
        let kA  = op_qubits a
            kB  = op_qubits b
            fA = evalOpMat a kA (pow2 kB * r)
            fB = evalOpMat b kB (pow2 kA * r)
            fAxI = onLeftBlock  kA kB r fA
            fIxB = onRightBlock kA kB r fB
        in (fIxB . fAxI)

      C a           -> onSelector id      (sub a) (k-1) r 
      DirectSum a b -> onSelector (sub a) (sub b) (k-1) r 

      R axis θ | θ == 0 -> id
               | otherwise  -> \x -> let
                  t         = pi * fromRational θ / 2
                  c         = cos t :+ 0
                  s         = sin t :+ 0
                  i        = 0 :+ 1
                  (ϕ, px) = applyPauliProduct axis k r x
                in  (c .* x) .+  (i*s*ϕ) .* px
    
    sub a = let f = evalOpMat a (k-1) r in f
                    
          
--------------------------------------------------------------------------------
-- Public “backend semantics”: QOp -> OpT on full state tensors
--------------------------------------------------------------------------------

-- Convention: the runtime state is a rank-n tensor of shape [2,2,..,2] (n qubits).
-- evalOp uses only structural reshapes; it does not build global dense matrices.
evalOp op = \psi -> 
  let n = op_qubits op
      f = if n /= n_qubits psi
             then error $ "Dim-mismatch between " ++ showOp op ++ " and state with n="++show (n_qubits psi)
             else evalOpMat op n 1       
  in 
    fromWork (f (toWork psi))

evalStep (st, outs, rng) step = let n = n_qubits st in 
  case step of
    Unitary op | (n_qubits op == n) -> (apply (evalOp op) st, outs, rng)
               | otherwise -> error $ "Dim-mismatch between " ++ showOp op ++ " and n="++show n

    -- outcomes are latest-first, so ks is reversed on input
    Measure ks -> foldl (measure1) (st, outs, rng) (reverse ks)
    Initialize ks vs ->
      let
        (st', os, rng') = evalStep (st, [], rng) (Measure ks)
        -- List of outcomes xor values for each initialized qubit
        corrections     = zipWith xor os vs
        -- Now we build the full list, including unaffected qubits        
        corrFull        = accumArray xor False (0,n-1) (zip ks corrections)
        corrOp          = foldl (⊗) One [ if c then X else I | c <- elems corrFull ]
      in (evalStep) (st', outs, rng') (Unitary corrOp)

  -- | evalProg simply executes a program step by step
evalProg steps psi0 rng0 = foldl evalStep (psi0, [], rng0) steps

measure1 :: (StateT, Outcomes, RNG) -> Int -> (StateT, Outcomes, RNG)
measure1 (state, outcomes, (r:rng)) k = let
      n       = ilog2 (rows state)
      proj0 = measureProjection n k 0
      proj1 = measureProjection n k 1

      s0 = proj0 state
      s1 = proj1 state

      prob0 = (realPart $ inner state s0) :: Realnum StateT
      prob1 = (realPart $ inner state s1) :: Realnum StateT

      outcome = if (r < prob0) then False else True
      collapsed_state = normalize $ if(outcome) then s1 else s0

      in
          if (abs(prob1+prob0-1)>tol) then
              error $ "Probabilities don't sum to 1: " ++ (show (prob0,prob1))
          else
              (collapsed_state, outcome:outcomes, rng)


-- | Project a state onto outcome b∈{0,1} of qubit k (MSB-first indexing),
--   without renormalization.
--
-- State is treated as a (2^n × r) matrix (r=1 for a single ket; can be batch).
-- Row index i encodes the computational basis |i⟩ with qubit 0 as MSB.
-- The projection keeps rows whose k-th bit equals b and zeros the others.
measureProjection
  :: Int   -- ^ n: number of qubits
  -> Int   -- ^ k: qubit index (0 = MSB)
  -> Int   -- ^ b: outcome (0 or 1)
  -> WorkT -- ^ input state (2^n × r)
  -> WorkT -- ^ projected state (2^n × r)
measureProjection n k b st =
  let rowsN = 2^n
      colsR = cols st
      bitPos = n - 1 - k
      keep i = ((i `div` (2^bitPos)) `mod` 2) == b
  in make2 (rowsN, colsR) $ \(i,j) ->
       if keep i then index2 st (i,j) else 0



 

--------------------------------------------------------------------------------
-- Dagger (structural)
--------------------------------------------------------------------------------

dagger :: QOp -> QOp
dagger = \case
  Id n          -> Id n
  Phase q       -> Phase (-q)
  X             -> X
  Y             -> Y
  Z             -> Z
  H             -> H
  SX            -> Adjoint SX -- Do we need applySXdagger?
  R a theta     -> R a (-theta)
  C a           -> C (dagger a)
  Permute ks    -> Permute (invertPerm ks)
  Tensor a b    -> Tensor (dagger a) (dagger b)
  DirectSum a b -> DirectSum (dagger a) (dagger b)
  Compose a b   -> Compose (dagger b) (dagger a)
  Adjoint a     -> a
