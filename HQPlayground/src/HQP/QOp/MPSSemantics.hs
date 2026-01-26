{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}

module HQP.QOp.MPSSemantics
  ( Site(..), MPS(..), StateT, WorkT
  , Interval(..)
  , Trunc(..), EvalCfg(..), defaultCfg
  , ket, ketW, toSparseMat
  , measureProjection, measure1
  , apply, evalStep, evalProg
  , evalOp, evalOpAtW
  , dagger
  ) where
-- | TODO: 1. Query bond dimension
---        2. Track accumulated error
---        3. Clean up dirty bit (is it actually needed?)
---        4. Write documentation
---        5. Optimized multi-qubit rotation and multi-controlled gates
---        6. Drop WorkT, since we no longer have lazy evaluation?

import Data.Complex (Complex(..), conjugate, magnitude, realPart, imagPart)
import qualified Data.Vector as V
import Data.Vector ((!), Vector, (//))
import Data.Bits (shiftL, testBit, (.|.),xor)
import Data.List (foldl', sortOn)
import Data.Array (accumArray, elems)
import qualified Data.Set as S
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions (invertPerm, ilog2,integerlog2, toBits', op_support)
import HQP.PrettyPrint.PrettyMatrix 
import HQP.PrettyPrint.PrettyOp
import HQP.QOp.MatrixSemantics (CMat)
import qualified HQP.QOp.MatrixSemantics as MS

import Numeric.LinearAlgebra (
  (><), atIndex, tr, rows, cols, size, diagBlock, diag, compactSVD, compactSVDTol, dot, 
  takeRows,takeColumns,dropRows,dropColumns)
import qualified Numeric.LinearAlgebra as H
import Numeric.LinearAlgebra.Devel (foldVector)
import Debug.Trace (trace)
import GHC.Stack (HasCallStack, callStack, prettyCallStack)


type StateT = MPS
type WorkT  = MPS
type OpT    = StateT -> StateT
type CVec   = H.Vector ComplexT

apply :: (t -> t) -> t -> t
apply f x = f x

-- MPS representation
data Interval = Ival !Int !Int deriving (Show,Eq)
hull :: Interval -> Interval -> Interval
hull (Ival l r) (Ival l' r') = Ival (min l l') (max r r')

singletonIval :: Int -> Interval
singletonIval p = Ival p p

-- A : Dl x 2 x Dr as (A0,A1), each Dl x Dr.
data Site = Site { a0 :: !CMat, a1 :: !CMat } deriving (Show,Eq)
-- MPS in physical chain order; Permute updates only maps.
data MPS = MPS
  { scalar     :: !ComplexT
  , sites      :: !(Vector Site)
  , center_site :: !Int
  , log2phys   :: !(Vector Int)
  , phys2log   :: !(Vector Int)
  , dirty      :: !(Maybe Interval)
  , cfg        :: !EvalCfg
  } deriving (Show,Eq)

nSites :: MPS -> Int
nSites = V.length . sites

instance HasQubits MPS where n_qubits = nSites

class HasWork t where
  toWork   :: t -> WorkT
  fromWork :: WorkT -> t
instance HasWork StateT where toWork = id; fromWork = id

invertVec :: Vector Int -> Vector Int
invertVec v =
  let n = V.length v
  in  (V.replicate n 0) // [ (p,q) | (q,p) <- zip [0..] (V.toList v) ]

instance HasTensorProduct MPS where (⊗) = tensorMPS

{-| tensor product a ⊗ b for MPS a,b -}
tensorMPS :: MPS -> MPS -> MPS
tensorMPS a b =
  let (na,nb) = (nSites a, nSites b)
      (a',b') = (moveCenterToPhys (na-1) a, moveCenterToPhys 0 b)
      l2p = V.generate (na+nb) $ \q -> if q < na then log2phys a ! q else na + log2phys b ! (q-na)
  in MPS { scalar      = scalar a * scalar b, 
           sites       = sites a V.++ sites b, 
           center_site = if na > 0 then center_site a else na + center_site b, 
           log2phys = l2p, 
           phys2log = invertVec l2p, 
           dirty = Nothing, 
           --dirty = Just (Ival (na-1) (na+1)),
           cfg = truncMax (cfg a) (cfg b) -- Worst accuracy guarantee determines overall accuracy
           }

{-| Combined truncation level: If we combine two MPS, use the least accurate truncation level -}
truncMax :: EvalCfg -> EvalCfg -> EvalCfg
truncMax c1 c2 = EvalCfg
  { trunc = case (trunc c1, trunc c2) of
      (Exact, t) -> t
      (t, Exact) -> t
      (Truncate m1 e1, Truncate m2 e2) -> Truncate (min m1 m2) (max e1 e2)
  , tol = max (tol c1) (tol c2)
  }


withSameFrame :: String -> WorkT -> WorkT -> (WorkT -> WorkT -> a) -> a
withSameFrame ctx x y k
  | nSites   x /= nSites   y = error (ctx ++ ": arity mismatch")
  | log2phys x /= log2phys y = error (ctx ++ ": wire-map mismatch") -- TODO: Rewire automatically?
  | otherwise                = k x y

scaleMPS :: ComplexT -> MPS -> MPS
scaleMPS c m = m { scalar = c * scalar m }

absorbScalarAt :: Int -> WorkT -> WorkT
absorbScalarAt p m
  | scalar m == (1:+0) = m
  | p < 0 || p >= nSites m = error "absorbScalarAt"
  | otherwise =
      let c = scalar m
          s = sites m ! p
          s' = Site (c .* (a0 s)) (c .* (a1 s))
      in m { scalar = 1:+0, sites = sites m V.// [(p,s')] } 

markDirtyIval :: Interval -> MPS -> MPS
markDirtyIval i m = m { dirty = Just $ maybe i (hull i) (dirty m) }

clearDirty :: MPS -> MPS
clearDirty m = m { dirty = Nothing }

(.*.) = (H.<>) -- HMatrix <> conflicts with Prelude.<>

innerMPS :: HasCallStack => WorkT -> WorkT -> ComplexT
innerMPS x0 y0 = -- trace ("innerMPS(" ++ showState x0 ++ ", " ++ showState y0 ++ ")") $      
  withSameFrame "innerMPS" x0 y0 $ \x y ->
  let n  = nSites x
      (sx, sy) = (scalar x, scalar y)
      e0 = foldl' step ((1><1) [1:+0]) [n-1, n-2 .. 0] -- Full sweep for contraction
      step e p = -- e is contraction accumulator ("environment" in MPS lingo), p is current site
        let Site xa0 xa1 = sites x ! p
            Site ya0 ya1 = sites y ! p
            --dims xs = map (\m -> (rows m, cols m)) xs
            term xs ys = --trace(show $ dims [xs,tr xs,e,ys]) $ 
                        ys .*. e .*. tr xs -- Contract with accumulator. Why are dims reversed at this point?
        in term xa0 ya0 + term xa1 ya1 -- Contract over 0,1 
      dotprod = conjugate sx * sy * (e0 `atIndex` (0,0))
  in 
    --trace("innerMPS = " ++ show dotprod) 
    dotprod

instance HilbertSpace WorkT where
  type Realnum WorkT = Double
  type Scalar  WorkT = ComplexT

  (.*) c ψ = scaleMPS c ψ
  (.+) ψ φ = addMPS ψ φ
  (.-) ψ φ = addMPS ψ (((-1):+0) .* φ)

  inner = innerMPS
  normalize ψ = let 
     nrm = norm ψ 
    in 
      if nrm < tol (cfg ψ) then ψ else ((1/nrm):+0) .* ψ
  
data Trunc = Exact | Truncate { maxBond :: !Int, eps2 :: !Double } deriving (Show,Eq)
data EvalCfg = EvalCfg { trunc :: !Trunc, tol :: !Double } deriving (Show,Eq)

defaultCfg :: EvalCfg
defaultCfg = EvalCfg { trunc = Exact, tol = 1e-12 }

-- structural dagger -- move to Syntax?
dagger :: QOp -> QOp
dagger = \case
  Id n          -> Id n
  Phase q       -> Phase (-q)
  X             -> X
  Y             -> Y
  Z             -> Z
  H             -> H
  SX            -> Adjoint SX
  R a t         -> R a (-t)
  C a           -> C (dagger a)
  Permute ks    -> Permute (invertPerm ks)
  Tensor a b    -> Tensor (dagger a) (dagger b)
  DirectSum a b -> DirectSum (dagger a) (dagger b)
  Compose a b   -> Compose (dagger b) (dagger a)
  Adjoint a     -> a

-- basis kets (logical MSB-first)
ketW :: [Int] -> WorkT
ketW bs =
  let n = length bs
      mk b = let v0 = if b==0 then 1:+0 else 0:+0
             in Site ((1><1) [v0]) ((1><1) [1-v0])
      ss  = V.fromList (map mk bs)
      idm = V.generate n id
  in MPS { scalar = 1:+0, sites = ss, center_site = 0, log2phys = idm, phys2log = idm, dirty = Nothing, cfg = defaultCfg }
ket :: [Int] -> StateT
ket = fromWork . ketW

-- wire permutation: logical relabeling only
applyPermute :: HasCallStack => Int -> [Int] -> WorkT -> WorkT
applyPermute base π m =
  let n    = length π
      l2p  = log2phys m
      sl   = V.slice base n l2p
      sl'  = V.fromList [ sl ! k | k <- π ]
      l2p' = l2p // [ (base+i, sl' ! i) | i <- [0..n-1] ]
      p2l' = invertVec l2p'
  in m { log2phys = l2p', 
         phys2log = p2l' }

-- small matrix helpers
hcat, vcat :: CMat -> CMat -> CMat
hcat = (H.|||)
vcat = (H.===)

{-| Dense matrix representation of two adjacent sites 
               [ A0 ]
     Θ2(A,B) = [ A1 ] [B0 B1] -}
theta2 :: Site -> Site -> CMat
theta2 a b = vcat (a0 a)  (a1 a) .*. hcat (a0 b) (a1 b)

chooseChi :: EvalCfg -> H.Vector Double -> Int
chooseChi cfg s =
  let ss    = H.toList s
      ssNZ  = takeWhile (> tol cfg) ss
      rNZ   = max 1 (length ssNZ)
      sq x  = x*x
  in case trunc cfg of
       Exact -> rNZ
       Truncate{maxBond, eps2} ->
         let cap = max 1 (min maxBond rNZ)
             tot = sum (map sq (take rNZ ss))
             ok chi = let kept = take chi ssNZ
                          tailE = tot - sum (map sq kept)
                      in tailE <= eps2 * tot
         in head ([chi | chi <- [1..cap], ok chi] ++ [cap])


diagMulLeft :: H.Vector Double -> CMat -> CMat
diagMulLeft v m = (H.complex . H.asColumn $ v) * m

diagMulRight :: CMat -> H.Vector Double -> CMat
diagMulRight m v = m * (H.complex . H.asRow $ v)

svd_chi :: EvalCfg -> CMat -> (CMat, H.Vector Double, CMat, Int)
svd_chi cfg m = case trunc cfg of
  Exact -> let 
              (u,s,v) = compactSVD m
              chi = size s
            in (u, s, v, chi)
  Truncate{maxBond, eps2} -> let (u,s,v) = compactSVDTol eps2 m -- TODO: Check def 
                                 chi     = min maxBond (size s)
                                 u'      = H.takeColumns chi u
                                 v'      = H.takeColumns chi v
                            in (u', s, v', chi)

moveRight :: Int -> WorkT -> WorkT
moveRight j m
  | j < 0 || j+1 >= nSites m = error "moveRight"
  | otherwise =
      let 
          (a, b)       = (sites m ! j, sites m ! (j+1))
          (dl, dr)     = (rows (a0 a), cols (a0 b)) -- External bond dimensions
          (u,s,v,chi)  = svd_chi (cfg m) (theta2 a b) -- compactSVD (exact or tol truncated) or thinSVD (maxbond truncated). χ is the new internal bond dimension
--          (u',v')  = H.takeColumns chi <$> (u,v)
          a'  = Site (takeRows dl u) (dropRows dl u) -- Left Isometry A'
          -- Absorb singular values into B'. Θ = U S V† = A' B'  =>  B' = S V† 
          sv  = diagMulLeft s (tr v)
          b'  = Site (takeColumns dr sv) (dropColumns dr sv)
      in m { sites = sites m V.// [(j,a'),(j+1,b')], center_site = j+1 }

moveLeft :: Int -> WorkT -> WorkT
moveLeft j m
  | j <= 0 || j >= nSites m = error "moveLeft"
  | otherwise =
      let i = j-1
          (a,b)       = (sites m ! i, sites m ! j)
          (dl, dr)    = (rows (a0 a), cols (a0 b))
          (u,s,v,chi) = svd_chi (cfg m) (theta2 a b)
          -- Absorb singular values into A'. Θ = U S V† = A' B'  =>  A' = U S
          us  = diagMulRight u s
          a'  = Site (takeRows dl us) (dropRows dl us)
          b'  = Site (takeColumns dr (tr v)) (dropColumns dr (tr v))
      in m { sites = sites m V.// [(i,a'),(j,b')], center_site = j-1 }

moveCenterToPhys :: Int -> WorkT -> WorkT
moveCenterToPhys p0 = go where
  go !m | center_site m < p0 = go (moveRight (center_site m) m)
        | center_site m > p0 = go (moveLeft  (center_site m) m)
        | otherwise         = m

compressRange :: Interval -> WorkT -> WorkT
compressRange (Ival l r) m
  | r <= l    = m
  | otherwise = foldl' (\acc j -> moveRight j acc) m [l..r-1]

compressIfDirty :: WorkT -> WorkT
compressIfDirty m = case dirty m of
  Nothing -> m
  Just i  -> clearDirty (compressRange i m)
-- local 1-qubit gate on a physical site: A'_s = sum_t U_{s,t} A_t
type Gate1 = (ComplexT,ComplexT,ComplexT,ComplexT) -- (u00,u01,u10,u11)

apply1Phys :: Gate1 -> Int -> WorkT -> WorkT
apply1Phys (u00,u01,u10,u11) p m =
  let s = sites m ! p
      a0' = u00 .* (a0 s) + u01 .* (a1 s)
      a1' = u10 .* (a0 s) + u11 .* (a1 s)
  in markDirtyIval (singletonIval p) $ m { sites = sites m V.// [(p, Site a0' a1')] }

apply1Logical :: Int -> Int -> Gate1 -> WorkT -> WorkT
apply1Logical base k u m = apply1Phys u (log2phys m ! (base+k)) m

pauliGate :: QOp -> Gate1
pauliGate = \case
  X -> (0,1,1,0)
  Y -> (0, 0:+(-1), 0:+1, 0)
  Z -> (1,0,0,-1)
  _ -> error "pauliGate"

cisPi :: Rational -> ComplexT
cisPi q = let t = pi * fromRational q in cos t :+ sin t
-- axis is Phase * Pauli-string in Tensor form (type-checked upstream)
-- returns (global phase phi, per-qubit operator list)
axisPaulis :: Int -> QOp -> (ComplexT, [QOp])
axisPaulis n = go (1:+0) where
  go !ϕ op = case op of
    Id m      -> (ϕ, replicate m (Id 1))
    Phase q   -> (ϕ * cisPi q, replicate n (Id 1))
    X         -> (ϕ, [X])
    Y         -> (ϕ, [Y])
    Z         -> (ϕ, [Z])
    
    Tensor a b ->
      let (ϕ1,p1) = axisPaulis (op_qubits a) a
          (ϕ2,p2) = axisPaulis (op_qubits b) b
      in (ϕ*ϕ1*ϕ2, p1++p2)

    -- TODO: Allow Compose 


    Adjoint a -> let (ϕ1,ps) = axisPaulis n a in (conjugate ϕ * ϕ1, ps)

    _         -> error "axisPaulis: axis not Pauli string"

applyPauliString :: Int -> QOp -> WorkT -> (ComplexT, WorkT, Interval)
applyPauliString base axis m =
  let n = op_qubits axis
      (ϕ, ops) = axisPaulis n axis
      actIdx = op_support axis      
      phys   = [ log2phys m ! (base+i) | i <- S.toList actIdx ]
      iSupp = case phys of
                [] -> singletonIval (log2phys m ! base)
                _  -> Ival (minimum phys) (maximum phys)
      m' = foldl' (\acc i -> case ops !! i of
                               Id _ -> acc
                               g    -> apply1Logical base i (pauliGate g) acc
                   ) m [0..n-1]
  in (ϕ, m', iSupp)

-- local addition with branch-index only on a hull, followed by local compression
addLocal :: Interval -> WorkT -> WorkT -> WorkT
addLocal (Ival l r) ψ0 φ0 = withSameFrame "addLocal" ψ0 φ0 $ \ψ φ ->
    if      scalar ψ == 0 then φ0
    else if scalar φ == 0 then ψ0
    else let 
        (ψ1,φ1) = (absorbScalarAt l ψ, absorbScalarAt l φ)
        (sψ, sφ) = (sites ψ1, sites φ1)

        mk p -- TODO: simplify
          | p < l || p > r = sψ ! p    -- Outside supp(a b^{-1}) caller promises ψ[p] = φ[p]
          | l == r = let a = sψ ! p; b = sφ ! p -- Singleton support TODO: check formula
                     in Site (a0 a + a0 b) (a1 a + a1 b)
          | p == l = let a = sψ ! p; b = sφ ! p -- Left edge: horizontal entry Dl x (2Dr)
                     in Site (hcat (a0 a) (a0 b)) (hcat (a1 a) (a1 b))
          | p == r = let a = sψ ! p; b = sφ ! p -- Right edge: vertical exit (2Dl) x Dl
                     in Site (vcat (a0 a) (a0 b)) (vcat (a1 a) (a1 b))
          | otherwise = let a = sψ ! p; b = sφ ! p -- Internal: block diagonal (2Dl) x (2Dl)
                      in Site (diagBlock [a0 a, a0 b]) (diagBlock [a1 a, a1 b])

        out = ψ1 { scalar = 1:+0, 
                   sites  = V.generate (nSites ψ1) mk }
  in compressRange (Ival l r) out

addMPS :: WorkT -> WorkT -> WorkT
addMPS ψ φ =
  let n = nSites ψ
      i = case (dirty ψ, dirty φ) of
            (Just a, Just b) -> hull a b
            (Just a, Nothing) -> a
            (Nothing, Just b) -> b
            (Nothing, Nothing) -> Ival 0 (max 0 (n-1))
  in addLocal i ψ φ

mulVecMat :: CVec -> CMat -> CVec
mulVecMat v m = H.flatten (H.asRow v .*. m)

-- beam-search sparse extraction (fast for low-entanglement states)
toSparseMat :: (HasWork t) => Double -> Int -> t -> SparseMat
toSparseMat eps maxTerms t0 =
  let mps = compressIfDirty (toWork t0)
      n   = fromIntegral . nSites $ mps
      dim = 2^n :: Integer
      -- states are (index, row-vector on current bond)
      step states p =
        let Site x0 x1 = sites mps ! p
            q = phys2log mps ! p
            bitpos = n-1-q
            extend (idx,v) =
              [ let m = if s==0 then x0 else x1
                    v' = mulVecMat v m
                    w2 = H.sumElements (H.cmap (\z -> let a=realPart z; b=imagPart z in a*a+b*b) v')
                    idx' = if s==0 then idx else (idx .|. (1 `shiftL` bitpos))
                in (idx', v', w2)
              | s <- [0,1] :: [Int]
              ]
            cand = concatMap extend states
            cand' = [ (i,v,w2) | (i,v,w2) <- cand, sqrt w2 > eps ]
            best = take maxTerms $ sortOn (\(_,_,w2) -> negate w2) cand'
        in [ (i,v) | (i,v,_) <- best ]
      finals = foldl' step [(0, H.fromList [scalar mps])] [0..n-1]
      nz = [ ((i,0), v `H.atIndex` 0) | (i,v) <- finals, H.size v == 1, magnitude (v `H.atIndex` 0) > eps ]
  in trace ("nSites = "++show n++", dim = "++show dim) SparseMat ((dim,1), nz)

instance Convertible WorkT SparseMat where
  to   mps = toSparseMat (tol $ cfg mps) 100 mps
  from = \sm ->
    let (SparseMat ((m,_), nonzeros)) = sm
        n = integerlog2 m
        kets = [ a .* ketW (toBits' n k) | ((k,_),a) <- nonzeros ] :: [WorkT]
    in case kets of
         [] -> error "fromSparseMat: empty"
         (x:xs) -> foldl' (.+) x xs


instance Convertible StateT CMat where
  to psi = 
    let (SparseMat ((m,_), nonzeros)) = to psi :: SparseMat
        n = integerlog2 m
        kets  = [a .* (MS.ket $ toBits' n k) | ((k,_),a) <- nonzeros] :: [CMat]
    in
      foldr1 (.+) kets
           
  from psimat = 
    let psi_sparse = MS.sparseMat psimat 
    in from psi_sparse :: StateT

-- measurement
frob2 :: CMat -> Double
frob2 x =
  let v = H.flatten x
  in realPart $ dot v v -- Hmatrix conjugates left argument to dot

-- | TODO: Clean up compressIfDirty mess.
projectCtrl :: Int -> Bool -> WorkT -> WorkT
projectCtrl p one m =
  let m0 = moveCenterToPhys p (compressIfDirty m)
  in projectCenter p one  m0

-- | Project the *center* site to |b> (b=False => |0>, True => |1>).
--   Produces an *unnormalized* post-measurement state.
projectCenter :: Int -> Bool -> MPS -> MPS
projectCenter p b st =
  let Site x0 x1 = sites st V.! p
      (y0,y1)    = if b then (zeros_like x0, x1) else (x0, zeros_like x1)
  in st { sites = sites st V.// [(p, Site y0 y1)]
        , dirty = Just (singletonIval p)
        }

measureProjection :: (HasCallStack, HasWork t) => Int -> Int -> Int -> (t -> t)
measureProjection _arity k out t0 =
  let st0 = compressIfDirty (toWork t0)
      p   = log2phys st0 V.! k
      st2 = projectCenter p (out==1) st0
      st3 = clearDirty (compressRange (singletonIval p) st2)
  in
    --trace ("measureProjection on qubit " ++ show k ++ " to " ++ show out ++ 
    --       " of state " ++ showState st0 ++ "\n = " ++ showState st3) $ 
    fromWork st3


  
zeros_like :: CMat -> CMat
zeros_like x = H.konst (0:+0) (rows x, cols x)

-- | TODO: Simplify 
-- | TODO: Clean up compressIfDirty mess.
measure1 :: HasCallStack => (StateT, Outcomes, RNG) -> Int -> (StateT, Outcomes, RNG)
measure1 (st, outs, u:us) k = --trace("measure1 on qubit " ++ show k ++ " of state " ++ showState st) $
  let 
      st0 = compressIfDirty st
      p   = log2phys st0 ! k
      st1 = moveCenterToPhys p st0
      Site x0 x1 = sites st1 ! p
      s2  = let a = magnitude (scalar st1) in a*a
      p0  = s2 * frob2 x0
      p1  = s2 * frob2 x1
      tot = p0 + p1
  in if tot < (tol $ cfg st) then error "measure1: prob~0" else
     let b    = (u*tot >= p0)
         pb   = if b then p1 else p0
         inv  = (1 / sqrt pb) :+ 0
         y0   = if b then zeros_like x0 else inv .* x0
         y1   = if b then inv .* x1 else zeros_like x1
         st2  = st1 { sites = sites st1 V.// [(p, Site y0 y1)], dirty = Just (singletonIval p), cfg = cfg st1 }
         st3  = clearDirty (compressRange (singletonIval p) st2)
     in (st3, b:outs, us)
measure1 (_,_,[]) _ = error "measure1: empty RNG"

-- support interval (physical hull) from op_support
supportInterval :: WorkT -> Int -> QOp -> Interval
supportInterval st base op =
  let supL = S.toList (op_support op)
      ps   = [ log2phys st ! (base+q) | q <- supL ]
  in case sortOn id ps of
       [] -> singletonIval (log2phys st ! base)
       xs -> Ival (head xs) (last xs)

-- evaluator
evalOp :: QOp -> OpT
evalOp op = evalOpAtW 0 op 
  

evalOpAtW :: HasCallStack => Int -> QOp -> WorkT -> WorkT
evalOpAtW base op st = case op of
  Id _      -> st
  Phase q   -> (cisPi q) .* st
  Permute π -> applyPermute base π st
  X  -> apply1Logical base 0 (pauliGate X) st
  Y  -> apply1Logical base 0 (pauliGate Y) st
  Z  -> apply1Logical base 0 (pauliGate Z) st
  H  -> let s = (1/sqrt 2):+0 in apply1Logical base 0 (s,s,s,-s) st
  SX ->
    let a = 0.5:+0.5
        b = 0.5:+(-0.5)
    in apply1Logical base 0 (a,a,b,a) st
  
  Tensor a b ->
    let st1 = evalOpAtW base a st
    in evalOpAtW (base + op_qubits a) b st1
  
  Compose a b ->
     evalOpAtW base a (evalOpAtW base b st)
  
  Adjoint a -> evalOpAtW base (dagger a) st
  
  R axis θ -- TODO: Optimize 1 qubit case
    | θ == 0 -> st
    | otherwise ->
        let t = pi * fromRational θ / 2
            c = cos t :+ 0
            s = sin t :+ 0
            iC = 0 :+ 1
            (phi, pst, iSupp) = applyPauliString base axis st
            ψ1 = c .* st
            ψ2 = (iC*s*phi) .* pst
        in addLocal iSupp ψ1 ψ2
  
  C a ->
    let ctrlP = log2phys st ! base
        iA    = supportInterval st (base+1) a
        iHull = hull (singletonIval ctrlP) iA
        b0    = projectCtrl ctrlP False st
        b1    = evalOpAtW  (base+1) a (projectCtrl ctrlP True st)
    in addLocal iHull b0 b1
  
  DirectSum a b ->
    let ctrlP = log2phys st ! base
        iA    = supportInterval st (base+1) a
        iB    = supportInterval st (base+1) b
        iHull = hull (singletonIval ctrlP) (hull iA iB)
        b0    = evalOpAtW (base+1) a (projectCtrl ctrlP False st)
        b1    = evalOpAtW (base+1) b (projectCtrl ctrlP True  st)
    in addLocal iHull b0 b1

-- Steps / programs
evalStep :: HasCallStack => (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
evalStep (st, outs, rng) step = -- trace("step "++showStep step ++ " on " ++ showState st) $ 
  case step of
  Unitary op -> (apply (evalOp op) st, outs, rng)
  Measure ks -> foldl' measure1 (st, outs, rng) (reverse ks)
  Initialize ks vs ->
      let
        n = n_qubits st
        (st', os, rng') = evalStep (st, [], rng) (Measure ks)
        -- List of outcomes xor values for each initialized qubit
        corrections     = zipWith xor os vs
        -- Now we build the full list, including unaffected qubits        
        corrFull        = accumArray xor False (0,n-1) (zip ks corrections)
        corrOp          = foldl (⊗) One [ if c then X else I | c <- elems corrFull ]
      in (evalStep) (st', outs, rng') (Unitary corrOp)

evalProg :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG)
evalProg prog st rng = foldl' evalStep (st, [], rng) prog

maxBondDimension :: MPS -> Int
maxBondDimension mps =
  let ds = V.toList $ sites mps
      bondDims s = [ rows (a0 s), cols (a0 s) ]
  in maximum $ concatMap bondDims ds