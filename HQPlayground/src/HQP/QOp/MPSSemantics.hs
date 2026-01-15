{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}


module HQP.QOp.MPSSemantics
  ( -- * Types
    Site(..)
  , MPS(..)
  , StateT, WorkT
  , Trunc(..), EvalCfg(..), defaultCfg
  , ket, ketW, toSparseMat, measureProjection, measure1
  , apply, evalStep, evalProg
    -- * Core API
  , evalOp      -- :: QOp -> StateT -> StateT  (defaultCfg)
  , evalStep    -- :: QOp -> Int -> WorkT -> WorkT  (defaultCfg)
  , evalProg    -- :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG)  (defaultCfg)
  , evalOpCfg   -- :: EvalCfg -> QOp -> StateT -> StateT
  , evalOpAtW   -- :: EvalCfg -> Int -> QOp -> WorkT -> WorkT  (internal)
  , dagger
  ) where

import Data.Complex (Complex(..), conjugate,magnitude,realPart)
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Bits (shiftL, testBit,xor)
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions (invertPerm,ilog2,pow2,toBits')
import HQP.PrettyPrint.PrettyOp
import HQP.PrettyPrint.PrettyMatrix(showSparse)
import HQP.QOp.MatrixSemantics(CMat,CMatable(..)) -- TODO: Convertible t CMat
import qualified HQP.QOp.MatrixSemantics as MS
import Data.List (sortOn,foldl')
import Data.Array(accumArray,elems)
import Debug.Trace(trace)

import Data.Massiv.Array
  ( Array, Comp(Seq)
  , Ix2((:.)), Ix3, IxN(Ix3) 
  , Sz(..), Sz2, Sz3
  , size, makeArray
  , D, U
  )
import Data.Massiv.Array.Unsafe (unsafeIndex)
import qualified Data.Massiv.Array as A

import qualified Numeric.LinearAlgebra as HMat


type OpT = StateT -> StateT
type OpW = WorkT  -> WorkT

evalOp   :: QOp -> OpT
evalStep :: (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
evalProg :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG) 

apply :: (t->t) -> t -> t
apply f psi = f psi


--------------------------------------------------------------------------------
-- MPS representation
--------------------------------------------------------------------------------

type C = ComplexT

tol :: Double
tol = 1e-12

-- | A single site tensor A : Dl × 2 × Dr.
newtype Site r = Site { a :: Array r Ix3 C } -- TODO: Better name that doesn't conflict so easily.


-- | Mixed-canonical MPS (center tracking is present; canonicalization is TODO).
--
-- Representation of a (possibly approximate) n-qubit state:
--   |ψ⟩ = scalar · contraction(sites)
--
-- Convention:
--   * 'sites' are in physical chain order [0..n-1].
--   * 'log2phys' maps logical position -> physical site index.
--   * 'Permute' updates only (log2phys, phys2log) on the relevant logical slice.
data MPS r = MPS
  { scalar     :: !C
  , sites      :: !(Vector (Site r))
  , centerPhys :: !Int
  , log2phys   :: !(Vector Int)
  , phys2log   :: !(Vector Int)
  }

type StateT = MPS U
type WorkT  = MPS D

nSites :: MPS r -> Int
nSites = V.length . sites

--------------------------------------------------------------------------------
-- Work/manifest conversion (Massiv delayed internally; hmatrix only for SVD/QR later)
--------------------------------------------------------------------------------

class HasWork t where
  toWork   :: t -> WorkT
  fromWork :: WorkT -> t

instance HasWork WorkT where
  toWork   = id
  fromWork = id

instance HasWork StateT where
  toWork m =
    m { sites = V.map (\(Site x) -> Site (A.delay x)) (sites m) }
  fromWork m =
    m { sites = V.map (\(Site x) -> Site (A.computeAs A.U (A.setComp A.Par x))) (sites m) }

--------------------------------------------------------------------------------
-- Qubit count
--------------------------------------------------------------------------------

instance HasQubits (MPS r) where
  n_qubits = nSites

-----------------------------------------------------------------------------------
-- Constructing basis states
-----------------------------------------------------------------------------------
ketW :: [Int] -> WorkT
ketW bs =
  let n = length bs
      mkSite b = Site $ makeArray Seq (Sz3 1 2 1) $ 
                 \(Ix3 _ s _) -> if s == b then 1 :+ 0 else 0
      ss  = V.fromList (map mkSite bs)
      idm = V.generate n id
  in MPS { scalar     = 1 :+ 0
         , sites      = ss
         , centerPhys = 0
         , log2phys   = idm
         , phys2log   = idm
         }

ket :: [Int] -> StateT
ket = fromWork . ketW


--------------------------------------------------------------------------------
-- Tensor product (needed for HilbertSpace superclass constraint)
--------------------------------------------------------------------------------

instance HasTensorProduct (MPS r) where
  (⊗) = tensorMPS

tensorMPS :: MPS r -> MPS r -> MPS r
tensorMPS a b =
  let na = nSites a
      nb = nSites b
      s  = scalar a * scalar b
      ss = sites a V.++ sites b
      l2p =
        V.generate (na+nb) $ \q ->
          if q < na then (log2phys a V.! q)
                    else na + (log2phys b V.! (q-na))
      p2l = invertVec l2p
      c   = if na > 0 then centerPhys a else na + centerPhys b
  in MPS { scalar = s, sites = ss, centerPhys = c, log2phys = l2p, phys2log = p2l }

invertVec :: Vector Int -> Vector Int
invertVec l2p =
  let n = V.length l2p
  in V.replicate n 0 V.// [ (p,q) | (q,p) <- zip [0..] (V.toList l2p) ]

--------------------------------------------------------------------------------
-- Frame alignment primitive
--------------------------------------------------------------------------------

-- | Require same length and same logical wire frame (log2phys). Centralizes checks.
withSameFrame :: String -> WorkT -> WorkT -> (WorkT -> WorkT -> a) -> a
withSameFrame ctx x y k
  | nSites x /= nSites y
  = error (ctx ++ ": different number of sites")
  | log2phys x /= log2phys y
  = error (ctx ++ ": different wire mapping (Permute mismatch)")
  | otherwise
  = k x y

--------------------------------------------------------------------------------
-- Scalar handling primitives
--------------------------------------------------------------------------------

-- | Multiply into scalar field (cheap, exact).
scaleMPS :: C -> MPS r -> MPS r
scaleMPS c mps = mps { scalar = c * scalar mps }

-- | Absorb 'scalar' into the first site tensor (exact).
-- This provides a "network-only" normal form with scalar=1, used by addMPS.
pushScalarToFirstSite :: WorkT -> WorkT
pushScalarToFirstSite m
  | scalar m == (1:+0) = m
  | nSites m == 0      = m
  | otherwise =
      let c = scalar m
          Site t0 = sites m V.! 0
          Sz3 dl _ dr = size t0
          t0' = makeArray Seq (Sz3 dl 2 dr) $ \(Ix3 i s k) ->
                  c * unsafeIndex t0 (Ix3 i s k)
      in m { scalar = 1:+0, sites = sites m V.// [(0, Site t0')] }

--------------------------------------------------------------------------------
-- Hilbert space structure (scalar mult, addition/subtraction, inner product)
--------------------------------------------------------------------------------

instance HilbertSpace StateT where
  type Realnum StateT = Double
  type Scalar  StateT = ComplexT

  (.*) c ψ = fromWork $ c .* toWork ψ
  (.+) ψ φ = fromWork $ toWork ψ .+ toWork φ
  (.-) ψ φ = fromWork $ toWork ψ .- toWork φ

  inner ψ φ = inner (toWork ψ) (toWork φ)

  normalize ψ =
    let nrm = norm ψ
    in if nrm < tol then ψ else ((1/nrm) :+ 0) .* ψ

instance HilbertSpace WorkT where
  type Realnum WorkT = Double
  type Scalar  WorkT = ComplexT

  (.*) c ψ = scaleMPS c ψ
  (.+) ψ φ = addMPS ψ φ
  (.-) ψ φ = addMPS ψ (((-1):+0) .* φ)

  inner ψ φ = innerMPS ψ φ

  normalize ψ =
    let nrm = norm ψ
    in if nrm < tol then ψ else ((1/nrm) :+ 0) .* ψ

--------------------------------------------------------------------------------
-- Evaluation configuration
--------------------------------------------------------------------------------

data Trunc
  = Exact
  | Truncate { maxBond :: !Int, eps2 :: !Double }
  deriving (Show,Eq)

data EvalCfg = EvalCfg
  { trunc :: !Trunc
  }
  deriving (Show,Eq)

defaultCfg :: EvalCfg
defaultCfg = EvalCfg { trunc = Exact }

--------------------------------------------------------------------------------
-- Structural dagger (TODO: move common stuff to common module)
--------------------------------------------------------------------------------

dagger :: QOp -> QOp
dagger = \case
  Id n          -> Id n
  Phase q       -> Phase (-q)
  X             -> X
  Y             -> Y
  Z             -> Z
  H             -> H
  SX            -> Adjoint SX
  R a theta     -> R a (-theta)
  C a           -> C (dagger a)
  Permute ks    -> Permute (invertPerm ks)
  Tensor a b    -> Tensor (dagger a) (dagger b)
  DirectSum a b -> DirectSum (dagger a) (dagger b)
  Compose a b   -> Compose (dagger b) (dagger a)
  Adjoint a     -> a

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

evalOp = evalOpCfg defaultCfg

evalOpCfg :: EvalCfg -> QOp -> StateT -> StateT
evalOpCfg cfg op st =
  let n  = op_qubits op
      n0 = n_qubits st
  in if n /= n0
       then error $ "Dim-mismatch between op_qubits=" ++ show n ++ " and state n=" ++ show n0
       else fromWork (evalOpAtW cfg 0 op (toWork st))

--------------------------------------------------------------------------------
-- Internal: compositional evaluation on logical slices (offsets induced only by Tensor)
--------------------------------------------------------------------------------

evalOpAtW :: EvalCfg -> Int -> QOp -> WorkT -> WorkT
evalOpAtW cfg base op0 = trace (show op0) $ go op0
  where
    go = \case
      Id _       -> id

      Phase q    ->
        let ph = exp (0 :+ (pi * fromRational q))
        in scaleMPS ph

      X          -> apply1Logical base matX
      Y          -> apply1Logical base matY
      Z          -> apply1Logical base matZ
      H          -> apply1Logical base matH
      SX         -> apply1Logical base matSX

      Permute ks -> permuteLogicalSlice base ks

      Compose a b -> go a . go b
      Adjoint a   -> go (dagger a)

      Tensor a b  ->
        let kA = op_qubits a
        in evalOpAtW cfg base a . evalOpAtW cfg (base + kA) b

      -- Pauli-string rotation (no exponentiation):
      -- exp(i*pi*θ/2 * P) = cos(t) I + i sin(t) P,  t=pi*θ/2
      --
      -- Initial implementation: form linear combination of two MPS and compress (TODO).
      R axis θ
        | θ == 0    -> id
        | otherwise ->
            \mps ->
              let t          = pi * fromRational θ / 2
                  c          = cos t :+ 0
                  s          = sin t :+ 0
                  iC         = 0 :+ 1
                  (phi, pψ)  = applyPauliStringAt base axis mps
                  ψ1         = c .* mps
                  ψ2         = (iC*s*phi) .* pψ
              in compressAll cfg (ψ1 .+ ψ2)

      DirectSum a b ->
        \mps ->
          let -- branch control=0
              ψ0  = apply1Logical base matP0 mps
              ψ0' = evalOpAtW cfg (base + 1) a ψ0

              -- branch control=1
              ψ1  = apply1Logical base matP1 mps
              ψ1' = evalOpAtW cfg (base + 1) b ψ1
          in compressAll cfg (ψ0' .+ ψ1')

      C a ->
        \mps ->
          let n   = op_qubits a
              ψ0  = apply1Logical base matP0 mps              -- (P0 ⊗ I)ψ
              ψ1  = apply1Logical base matP1 mps              -- (P1 ⊗ I)ψ
              ψ1' = evalOpAtW cfg (base + 1) a ψ1             -- (P1 ⊗ a)ψ
          in compressAll cfg (ψ0 .+ ψ1')

--------------------------------------------------------------------------------
-- 2x2 matrices for 1-qubit gates (row = output, col = input)
--------------------------------------------------------------------------------

matX, matY, matZ, matH, matSX, matP0, matP1 :: ((C,C),(C,C))
matP0 = ((1,0),(0,0)) -- projector |0><0|
matP1 = ((0,0),(0,1)) -- projector |1><1|
matX = ((0,1),(1,0))
matZ = ((1,0),(0,-1))
matY = ((0, 0 :+ (-1)), (0 :+ 1, 0))         -- [[0,-i],[i,0]]
matH = let s = (1 / sqrt 2) :+ 0 in ((s,s),(s,-s))
matSX =
  let h = 0.5 :+ 0
      p = 1 :+ 1
      q = 1 :+ (-1)
  in ((h*p, h*q),(h*q, h*p))

--------------------------------------------------------------------------------
-- Local 1-qubit gate application on one logical wire (no swaps; uses mapping)
--------------------------------------------------------------------------------

apply1Logical :: Int -> ((C,C),(C,C)) -> WorkT -> WorkT
apply1Logical q u mps =
  let p = log2phys mps V.! q
      Site t = sites mps V.! p
      t' = applyU u t
  in mps { sites = sites mps V.// [(p, Site t')] }

applyU :: ((C,C),(C,C)) -> Array D Ix3 C -> Array D Ix3 C
applyU ((u00,u01),(u10,u11)) arr =
  let Sz3 dl _ dr = size arr
  in makeArray Seq (Sz3 dl 2 dr) $ \(Ix3 i s k) ->
       let a0 = unsafeIndex arr (Ix3 i 0 k)
           a1 = unsafeIndex arr (Ix3 i 1 k)
       in case s of
            0 -> u00*a0 + u01*a1
            _ -> u10*a0 + u11*a1

--------------------------------------------------------------------------------
-- Permute on a logical slice: update (log2phys, phys2log) only
--------------------------------------------------------------------------------

permuteLogicalSlice :: Int -> [Int] -> WorkT -> WorkT
permuteLogicalSlice base ks mps =
  let k    = length ks
      l2p  = log2phys mps
      slice  = V.generate k (\i -> l2p V.! (base+i))
      slice' = V.generate k (\i -> slice V.! (ks !! i))
      l2p' = l2p V.// [ (base+i, slice' V.! i) | i <- [0..k-1] ]
      p2l' = invertVec l2p'
  in mps { log2phys = l2p', phys2log = p2l' }

--------------------------------------------------------------------------------
-- Pauli-string application (restricted axis)
--------------------------------------------------------------------------------

-- | Apply a Pauli string (times global phase) on the logical slice starting at 'base'.
-- Restriction in this initial file:
--   axis may contain only Id, Phase, X,Y,Z, Tensor, Compose, Adjoint.
--   (No Permute, no H, no C, no DirectSum, no R.)
applyPauliStringAt :: Int -> QOp -> WorkT -> (C, WorkT)
applyPauliStringAt base axis mps = go axis mps
  where
    go :: QOp -> WorkT -> (C, WorkT)
    go = \case
      Id _       -> \x -> (1:+0, x)
      Phase q    -> \x -> (exp (0 :+ (pi * fromRational q)), x)

      X          -> \x -> (1:+0, apply1Logical base matX x)
      Y          -> \x -> (1:+0, apply1Logical base matY x)
      Z          -> \x -> (1:+0, apply1Logical base matZ x)

      Tensor a b ->
        let kA = op_qubits a
        in \x ->
            let (pA, x1) = applyPauliStringAt base a x
                (pB, x2) = applyPauliStringAt (base + kA) b x1
            in (pA*pB, x2)

      Compose a b ->
        \x -> let (pB, x1) = go b x
                  (pA, x2) = go a x1
              in (pA*pB, x2)

      Adjoint a  -> go (dagger a)

      _ -> error "applyPauliStringAt: non-Pauli constructor encountered (or Permute present)"

--------------------------------------------------------------------------------
-- Linear combination: addMPS
--------------------------------------------------------------------------------
-- Mathematical definition (open boundary, same length n):
--
--   |ψ⟩ = Σ_{s1..sn} A1^{s1} A2^{s2} ... An^{sn} |s1..sn⟩
--   |φ⟩ = Σ_{s1..sn} B1^{s1} B2^{s2} ... Bn^{sn} |s1..sn⟩
--
-- Define bond spaces by direct sum:
--   Cj = Aj ⊕ Bj
--
-- New tensors:
--   site 1:  [A1  B1]
--   1<j<n:  diag(Aj, Bj)
--   site n:  [An; Bn]
--
-- Contraction yields |ψ⟩ + |φ⟩, bond dimensions add.
--------------------------------------------------------------------------------

addMPS :: WorkT -> WorkT -> WorkT
addMPS x0 y0 =
  withSameFrame "addMPS" x0 y0 $ \x0' y0' ->
    let n = nSites x0'
    in case n of
         0 -> x0' { scalar = scalar x0' + scalar y0' }  -- C^1
         1 ->
           let x = pushScalarToFirstSite x0'
               y = pushScalarToFirstSite y0'
           in x { sites = V.singleton (siteAdd (sites x V.! 0) (sites y V.! 0)) }
         _ ->
           let x = pushScalarToFirstSite x0'
               y = pushScalarToFirstSite y0'
               sL   = siteHCatR    (sites x V.! 0)     (sites y V.! 0)
               sR   = siteVCatL    (sites x V.! (n-1)) (sites y V.! (n-1))
               mids = V.generate (n-2) (\j -> siteBlockDiag (sites x V.! (j+1)) (sites y V.! (j+1)))
               ss   = V.concat [V.singleton sL, mids, V.singleton sR]
           in x { sites = ss }  -- x has scalar=1 after push

--------------------------------------------------------------------------------
-- Site-level primitives for addMPS
--------------------------------------------------------------------------------

siteAdd :: Site D -> Site D -> Site D
siteAdd (Site a1) (Site a2) =
  let Sz3 dl1 _ dr1 = size a1
      Sz3 dl2 _ dr2 = size a2
  in if (dl1,dr1) /= (dl2,dr2)
       then error "siteAdd: mismatched bond dims"
       else Site $ makeArray Seq (Sz3 dl1 2 dr1) $ \(Ix3 l s r) ->
              unsafeIndex a1 (Ix3 l s r) + unsafeIndex a2 (Ix3 l s r)

-- | Left boundary: [A B] concatenation on right bond (Dl must be 1 in both).
siteHCatR :: Site D -> Site D -> Site D
siteHCatR (Site a1) (Site a2) =
  let Sz3 dl1 _ dr1 = size a1
      Sz3 dl2 _ dr2 = size a2
  in if dl1 /= 1 || dl2 /= 1
       then error "siteHCatR: expected Dl=1 at left boundary"
       else Site $ makeArray Seq (Sz3 1 2 (dr1+dr2)) $ \(Ix3 _ s r) ->
              if r < dr1 then unsafeIndex a1 (Ix3 0 s r)
                         else unsafeIndex a2 (Ix3 0 s (r-dr1))

-- | Right boundary: [A; B] concatenation on left bond (Dr must be 1 in both).
siteVCatL :: Site D -> Site D -> Site D
siteVCatL (Site a1) (Site a2) =
  let Sz3 dl1 _ dr1 = size a1
      Sz3 dl2 _ dr2 = size a2
  in if dr1 /= 1 || dr2 /= 1
       then error "siteVCatL: expected Dr=1 at right boundary"
       else Site $ makeArray Seq (Sz3 (dl1+dl2) 2 1) $ \(Ix3 l s _) ->
              if l < dl1 then unsafeIndex a1 (Ix3 l s 0)
                         else unsafeIndex a2 (Ix3 (l-dl1) s 0)

-- | Middle sites: block diagonal embedding on both bonds.
siteBlockDiag :: Site D -> Site D -> Site D
siteBlockDiag (Site a1) (Site a2) =
  let Sz3 dl1 _ dr1 = size a1
      Sz3 dl2 _ dr2 = size a2
      dl = dl1 + dl2
      dr = dr1 + dr2
  in Site $ makeArray Seq (Sz3 dl 2 dr) $ \(Ix3 l s r) ->
        case (l < dl1, r < dr1) of
          (True , True ) -> unsafeIndex a1 (Ix3 l s r)
          (False, False) -> unsafeIndex a2 (Ix3 (l-dl1) s (r-dr1))
          _              -> 0

--------------------------------------------------------------------------------
-- Inner product <ψ|φ> via transfer matrices
--------------------------------------------------------------------------------

-- Transfer step: Given the intermedite contraction "env" E_{lA,lB},
-- and site tensors A (from ⟨ψ|) and B (from |φ⟩), produce the updated
-- contraction E'_{rA,rB} after absorbing these sites.
--   E'_{rA,rB} = Σ_{lA,lB,s} conj(A_{lA,s,rA}) * E_{lA,lB} * B_{lB,s,rB}
transferStep :: Array D Ix2 C -> Site D -> Site D -> Array D Ix2 C
transferStep env (Site aA) (Site aB) =
  let Sz3 dlA _ drA = size aA
      Sz3 dlB _ drB = size aB
      Sz2 elA elB   = size env
  in if (elA,elB) /= (dlA,dlB)
       then error "transferStep: environment dims mismatch"
       else makeArray Seq (Sz (drA :. drB)) $ \(ra :. rb) ->
              let accumLB acc la lb =
                    let e = unsafeIndex env (la :. lb)
                        a0 = conjugate (unsafeIndex aA (Ix3 la 0 ra))
                        a1 = conjugate (unsafeIndex aA (Ix3 la 1 ra))
                        b0 = unsafeIndex aB (Ix3 lb 0 rb)
                        b1 = unsafeIndex aB (Ix3 lb 1 rb)
                    in acc + a0*e*b0 + a1*e*b1
                  accumLA acc la = foldl (\acc' lb -> accumLB acc' la lb) acc [0..dlB-1]
              in foldl accumLA (0:+0) [0..dlA-1]


innerMPS :: WorkT -> WorkT -> C
innerMPS x y =
  withSameFrame "inner" x y $ \x' y' ->
    let sx = scalar x'
        sy = scalar y'
        env0 = makeArray Seq (Sz (1 :. 1)) $ \(_ :. _) -> 1:+0
        envN = V.foldl' (\e (sa,sb) -> transferStep e sa sb) env0 (V.zip (sites x') (sites y'))
    in (conjugate sx * sy) * unsafeIndex envN (0 :. 0)

--------------------------------------------------------------------------------
-- Compression / canonicalization
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Compression via two-site SVD
--------------------------------------------------------------------------------

-- | Build the two-site matrix M = reshape(Θ) across bond (j,j+1):
--   A : Dl×2×Dm,  B : Dm×2×Dr
--   M : (Dl*2) × (2*Dr)
--   M[(la,s),(t,rb)] = Σ_m A[la,s,m] * B[m,t,rb]
mergeTwoSites :: Site D -> Site D -> Array D Ix2 C
mergeTwoSites (Site a1) (Site a2) =
  let Sz3 dl _ dm1 = size a1
      Sz3 dm2 _ dr = size a2
  in if dm1 /= dm2
       then error "mergeTwoSites: bond mismatch"
       else
         let rows = dl * 2
             cols = 2 * dr
         in makeArray Seq (Sz (rows :. cols)) $ \(r :. c) ->
              let (la, s) = r `divMod` 2
                  (t , rb) =
                    if c < dr then (0, c) else (1, c - dr)
                  go m acc =
                    acc + unsafeIndex a1 (Ix3 la s m) * unsafeIndex a2 (Ix3 m t rb)
              in foldr go (0:+0) [0..dm1-1]

-- | Convert a Massiv Ix2 matrix to an hmatrix Matrix (row-major).
toHMat2 :: Array D Ix2 C -> HMat.Matrix C
toHMat2 arr =
  let Sz2 r c = size arr
      xs = [ unsafeIndex arr (i :. j) | i <- [0..r-1], j <- [0..c-1] ]
  in (r HMat.>< c) xs

-- | Convert an hmatrix Matrix back to a Massiv Ix2 matrix (row-major).
fromHMat2 :: HMat.Matrix C -> Array D Ix2 C
fromHMat2 m =
  let r  = HMat.rows m
      c  = HMat.cols m
      xs = HMat.toList (HMat.flatten m)  -- row-major
  in makeArray Seq (Sz2 r c) $ \(i :. j) -> xs !! (i*c + j)

-- | Pick χ from singular values (descending).
chooseChi :: Trunc -> HMat.Vector Double -> Int
chooseChi tr s =
  let ss    = HMat.toList s
      ssNZ  = takeWhile (> tol) ss
      rNZ   = max 1 (length ssNZ)
      sq x  = x*x
  in case tr of
       Exact -> rNZ
       Truncate{maxBond, eps2} ->
         let cap    = max 1 (min maxBond rNZ)
             tot    = sum (map sq (take rNZ ss))
             -- smallest chi <= cap such that tail energy <= eps2*tot
             ok chi =
               let kept = take chi ssNZ
                   tailE = tot - sum (map sq kept)
               in tailE <= eps2 * tot
             chi0 = head ([ chi | chi <- [1..cap], ok chi ] ++ [cap])
         in chi0

-- | Split U (Dl*2×χ) into A' : Dl×2×χ, and SVH (χ×(2*Dr)) into B' : χ×2×Dr.
splitTwoSites
  :: Int                 -- Dl
  -> Int                 -- Dr
  -> Int                 -- χ
  -> HMat.Matrix C            -- U'  (Dl*2 × χ)
  -> HMat.Matrix C            -- SVH' (χ × 2*Dr)
  -> (Site D, Site D)
splitTwoSites dl dr chi u' svh' =
  let aL = makeArray Seq (Sz3 dl 2 chi) $ \(Ix3 la s k) ->
             u' `HMat.atIndex` (la*2 + s, k)
      aR = makeArray Seq (Sz3 chi 2 dr) $ \(Ix3 k t rb) ->
             let col = if t == 0 then rb else dr + rb
             in svh' `HMat.atIndex` (k, col)
  in (Site aL, Site aR)

-- | Compress a single physical bond j (between sites j and j+1) by SVD,
-- keeping χ according to cfg.trunc.
compressBond :: EvalCfg -> Int -> WorkT -> WorkT
compressBond cfg j mps =
  let n = V.length (sites mps)
  in if j < 0 || j+1 >= n
       then error "compressBond: bond index out of range"
       else
         let Site a1 = sites mps V.! j
             Site a2 = sites mps V.! (j+1)
             Sz3 dl _ dm1 = size a1
             Sz3 dm2 _ dr = size a2
         in if dm1 /= dm2
              then error "compressBond: internal bond mismatch"
              else
                let m   = mergeTwoSites (Site a1) (Site a2)
                    hm  = toHMat2 m
                    (u, s, v) = HMat.svd hm
                    chi = chooseChi (trunc cfg) s

                    u'   = HMat.takeColumns chi u
                    -- SVH = Σ V†
                    sC   = HMat.cmap (:+ 0) (HMat.subVector 0 chi s)
                    sig  = HMat.diag sC
                    svh  = sig HMat.<> HMat.tr (HMat.takeColumns chi v)  -- V is cols=rank; takeColumns chi => Vχ
                    (sL, sR) = splitTwoSites dl dr chi u' svh

                    ss' = sites mps V.// [(j, sL), (j+1, sR)]
                in mps { sites = ss' }

-- | Global compression sweep (physical bonds 0..n-2).
-- Exact: keeps all σ>tol at every bond. Truncate: caps / drops by cfg.
compressAll :: EvalCfg -> WorkT -> WorkT
compressAll cfg mps =
  let n = V.length (sites mps)
  in if n <= 1
       then mps
       else foldl (\acc j -> compressBond cfg j acc) mps [0..n-2]



-- | Enumerate amplitudes of an MPS and return a sparse column-vector in the PrettyMatrix
--   pretty-printer format: ((dim,1), [((i,0), a_i)]).
toSparseMat :: (HasWork t) =>                 
     Double            -- ^ eps: keep |amp| > eps
  -> Int               -- ^ maxTerms: keep at most this many nonzeros (after sorting by |amp|)
  -> t
  -> SparseMat
toSparseMat eps maxTerms mps' =
  let mps = toWork mps'
      n   = nSites mps
      dim = 1 `shiftL` n
      amps =
        [ (i, amplitudeOfIndex i mps)
        | i <- [0 .. dim-1]
        ]
      nz =
        [ ((i,0), a)
        | (i,a) <- amps
        , magnitude a > eps
        ]
      nz' = take maxTerms $ sortOn (\(_,a) -> negate (magnitude a)) nz
  in SparseMat ((dim,1), nz')

fromSparseMat :: SparseMat -> WorkT
fromSparseMat (SparseMat ((m,_), nonzeros)) =
  let n    = ilog2 m
      kets = [ a .* ketW (toBits' n k) | ((k,_),a) <- nonzeros ] :: [WorkT]
      addC acc t = compressAll defaultCfg (acc .+ t)
  in case kets of
       []     -> error "fromSparseMat: empty (cannot represent a unit state)"
       (x:xs) -> foldl' addC x xs

-- | TODO: Add global SparseMat data type, make showState work with Convertible t SparseMat, 
-- | and generalize PrettyMatrix.hs
instance Convertible WorkT SparseMat where
  to   = toSparseMat tol 100
  from = fromSparseMat

instance Convertible StateT SparseMat where
  to   = (toSparseMat tol 100) . toWork
  from = fromWork . fromSparseMat

-- TODO: use convertible instead
instance CMatable WorkT where
  toCMat psi = 
    let (SparseMat ((m,_), nonzeros)) = toSparseMat tol 100 psi
        n = ilog2 m
        kets  = [a .* (MS.ket $ toBits' n k) | ((k,_),a) <- nonzeros] :: [CMat]
    in
      foldr1 (.+) kets
           
  fromCMat psimat = 
    let psi_sparse = MS.sparseMat psimat
    in  fromSparseMat psi_sparse

instance CMatable StateT where
  toCMat   = toCMat . toWork
  fromCMat = fromWork . fromCMat

-- logical bits, MSB = qubit 0
bitsOfIndex :: Int -> Int -> Vector Int
bitsOfIndex n i =
  V.generate n (\q -> if testBit i (n-1-q) then 1 else 0)

-- | amplitude for a basis index i (logical MSB-first convention)
amplitudeOfIndex :: Int -> WorkT -> ComplexT
amplitudeOfIndex i mps =
  let n    = nSites mps
      bits = bitsOfIndex n i
      -- physical-site bit is the bit of the logical wire that currently occupies that site
      bitAtPhys p = bits V.! (phys2log mps V.! p)
      -- contract left-to-right over physical chain
      !a0 = scalar mps
      !v0 = [a0]  -- length Dl=1
      vN  = V.ifoldl' (\v p (Site t) -> contractSite v t (bitAtPhys p))
                      v0
                      (sites mps)
  in case vN of
       [x] -> x
       _   -> error "amplitudeOfIndex: expected right boundary dimension = 1"

-- v (Dl)  and site tensor t (Dl×2×Dr) at fixed physical bit s -> new vector (Dr)
contractSite :: [ComplexT] -> Array D Ix3 ComplexT -> Int -> [ComplexT]
contractSite v t s =
  let Sz3 dl _ dr = size t
  in if length v /= dl
       then error "contractSite: Dl mismatch"
       else [ sum [ v!!l * unsafeIndex t (Ix3 l s r) | l <- [0..dl-1] ]
            | r <- [0..dr-1]
            ]

----------------------------------------------------------------------------
--- Measurement
----------------------------------------------------------------------------
measureProjection ::
     Int   -- ^ n: arity in qubits
  -> Int   -- ^ k: qubit index (0..n-1)
  -> Int  -- ^ b: outcome (False or True)
  -> (StateT -> StateT)
measureProjection n k b =
  let pb = if b /= 0 then matP1 else matP0
  in \psi ->
       let w = toWork psi
       in if n /= n_qubits w
            then error "measureProjection: arity mismatch"
            else if k < 0 || k >= n
                   then error "measureProjection: qubit index out of range"
                   else fromWork (apply1Logical k pb w)


-- | TODO: Saml alle de funktioner som er de samme (eller nemt kan blive de samme) for alle 
---        semantik-backendsne og flyt dem til et fælles modul. Men hvordan gør jeg så med StateT 
---        og WorkT uden at ende i det type-helvede, jeg brugte 3 dage på uden at komme i mål sidst?
measure1 :: (StateT, Outcomes, RNG) -> Int -> (StateT, Outcomes, RNG)
measure1 (_, _, []) _ = error "Random numbers exhausted."
measure1 (state, outcomes, (r:rng)) k = let
      n = n_qubits state
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
              