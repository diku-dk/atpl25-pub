{-# LANGUAGE TypeFamilies #-}

module HQP.QOp.MatrixSemantics where

import HQP.QOp.Syntax
import HQP.QOp.Simplify
import HQP.QOp.Semantics
import HQP.PrettyPrint.PrettyOp
import HQP.QOp.HelperFunctions
import Numeric.LinearAlgebra hiding(normalize,step,(<>)) -- the hmatrix library
import Data.Bits(shiftL,xor)
import Data.Array(accumArray,elems)
import Data.List(sort)
import Debug.Trace(trace)

type CMat = Matrix ComplexT
type RMat = Matrix RealT

data MatrixSemantics
{-| 
 evalOp :: Op -> CMat
 (evalOp op) evaluates the pure quantum operator op (defined in Circuit.hs) in the matrix semantics, and produces a complex matrix of dimension 2^n x 2^n (where n is the qubit-length of op)
-}
instance SemanticsBackend MatrixSemantics where
  type StateT MatrixSemantics = CMat
  type OpT    MatrixSemantics = CMat

  stateQubits = ilog2 . rows
  opQubits    = ilog2 . rows

  measure1 :: (CMat, Outcomes, RNG) -> Nat -> (CMat, Outcomes, RNG)
  measure1 (state, outcomes, (r:rng)) k = let
        n = ilog2 (rows state)
        proj0 = measureProjection n k 0
        proj1 = measureProjection n k 1

        s0 = proj0 <> state
        s1 = proj1 <> state

        prob0 = realPart $ inner state s0
        prob1 = realPart $ inner state s1

        outcome = if (r < prob0) then False else True
        collapsed_state = normalize $ if(outcome) then s1 else s0

        in
            if (abs(prob1+prob0-1)>tol) then
                error $ "Probabilities don't sum to 1: " ++ (show (prob0,prob1))
            else
                (collapsed_state, outcome:outcomes, rng)
  
  measure1 (_,_,[]) _ = error "No more random numbers. This never happens."

  {-| bra [v0,...,v_{n-1}] (where v_j is 0 or 1) is the adjoint state <v0 v1 ... v_{n-1}|. In the matrix representation, this is a row-vector in C^{2^n}, i.e. of dimension (1 >< 2^n). -}
  ket = ketM     
  evalOp = evalOpM
    
evalOpM :: QOp -> CMat
evalOpM op = case op of
        Id n -> ident (2^n)

        Phase q -> let theta = (realToFrac q * pi) :+ 0 
                   in  scalar (exp (ii*theta))

        I -> (2 >< 2) [1,0,
                   0,1]

        X -> (2 >< 2) [0,1,
                       1,0]

        Y -> (2 >< 2) [-ii, 0,
                        0, ii]

        Z -> (2 >< 2) [1,0,
                       0,-1]

        H -> let s = 1/sqrt 2
             in  s * ((2><2) [1, 1,
                             1,-1])

        SX -> evalOpM $ R X (1/2)

        R axis q -> 
            let mat  = evalOpM axis
                theta = (realToFrac q * pi) :+ 0 -- Haskell won't multiply real and complex numbers
            in
                matFunc exp ( (-ii*theta/2) .* mat )

        Permute ks -> let
                        n = length ks
                        dims = 1 `shiftL` n
                        indices = [ (i, foldl (\acc (bit,pos) -> acc + (bit `shiftL` pos)) 0 (zip (toBits' n i) ks)) | i <- [0..dims-1] ]
                        values  = replicate dims (1 :+ 0)
                    in
                        assoc (dims,dims) (0 :+ 0) (zip indices values)
                                            
        C op1          ->  let 
                            mop = evalOpM op1
                            mI  = ident (rows mop)
                        in
                            mI <+> mop -- |0><0| ⊗ I^n + |1><1| ⊗ op1
    
        Tensor    op1 op2 -> (evalOpM op1)  ⊗  (evalOpM op2)
        Compose   op1 op2 | (n_qubits op1 == n_qubits op2) -> (evalOpM op1)  ∘  (evalOpM op2)  
                      | otherwise -> error $ 
                       "\n\nDim-mismatch: " ++ showOp op1 ++ " ∘ " ++ showOp op2 ++ "\n"
        DirectSum op1 op2 | (n_qubits op1 == n_qubits op2) -> (evalOpM op1)  <+> (evalOpM op2)  
                      | otherwise -> error $ 
                       "\n\nDim-mismatch: " ++ showOp op1 ++ "<+>" ++ showOp op2 ++ "\n"
        Adjoint op1       -> adj $ evalOpM op1

ketM :: [Int] -> CMat
ketM []    = (1><1) [1]
ketM (v':vs) = 
      let 
          v = fromIntegral v' :+ 0 
      in 
          ((2><1) [1-v,v]) ⊗ (ketM vs)
--------------------------------------------------------------------------------

--  State contruction: An n-qubit state can be represented by a vector in C^{2^n} (we'll later see potentially more compact representations). 




{-| 'evalStep rng step state' evaluates a computational step (unitary or measurement) given the current state and returns the modified quantum state. 

To deal with random measurements in a pure functional setting, we treat a random number generator rng as an infinite list of numbers between 0 and 1. This allows the library to remain pure - IO comes in from program mains. 

We take a random number generator as the first parameter, read off the first element, and return
the remainder together with the updated quantum state.
-} 


{-| measure1 measures a single qubit, projecting the state on the subspace corresponding to the 
    outcome, and prepends the outcome to the list of outcomes -}
 

{-|
 - The tensor product of two operators in matrix representation a :: (m><n) and b :: (p><q) is the kronecker product c :: (m*p >< n*q) with entries c_{i*p+k, j*q+l} = a_{ij}*b_{kl} 

 - The direct sum of two operators in matrix representation a :: (m><n) and b :: (p><q) is the block-diagonal matrix c :: ((m+p) >< (n+q)) with a and b as blocks. Note that the additive dimension necessitates that a and b have the same dimensions for it to be realizable on qubits. 

 - The operator adjoint in matrix representation is the conjugate transpose.
-}    
instance HasTensorProduct CMat where
    (⊗) = kronecker

instance HasDirectSum CMat where
    (⊕) a b = fromBlocks [[a, zeros (rows a) (cols b)],
                          [zeros (rows b) (cols a), b]]
instance HasAdjoint CMat where
    adj = tr -- HMatrix confusingly defines conjugate transpose as 'tr' (standard trace notation)

instance HasQubits CMat where
    n_qubits op = ilog2 (rows op)

instance Operator CMat

{-| We implement ket-states as (n >< 1) matrices (= column vectors), and bra-states as (1 >< n) matrices (= row vectors). Thus StateT inherits the operator operations (recall that states
are also linear operators by Riesz representation), but we can also treat them like vectors,
so we implement the VectorSpace operations. -}
instance HilbertSpace CMat where
    type Scalar  CMat = ComplexT 
    type Realnum CMat = RealT
    
    (.*) = scale
    (.+) a b = a+b

    -- | inner a b is the usual dot product, with the adjoint coefficients complex conjugated
    inner a b = let 
            (m,n,p,q) = (rows a, cols a, rows b, cols b) 
        in
            if (m,n) == (p,q) then 
                sumElements (conj a * b)        
            else 
                error $ "inner: incompatible shapes " ++ (show (m,n)) ++ " != " ++ (show (p,q))

    normalize :: CMat -> CMat
    normalize s = let 
          n = (norm_2 (flatten s))
        in 
          if (n < tol) then s 
          else              s / scalar (n :+ 0)


{-|
 measureProjection n k result 
 
Builds the projection operator onto the subspace of C^{2^n} in which qubit k has value 'result'.
 
Construction of the operator:
I ⨷ ... ⨷ I ⨷ P ⨷ I ⨷ ... ⨷ I 
\-- k-1 --/                   /
 \------------ n ------------/
-}
measureProjection :: Int -> Int -> Int -> CMat
measureProjection n k v' = let     
        v = fromIntegral v' :+ 0  :: ComplexT
        p = (2><2) [(1-v), 0,
                    0,     v] :: CMat
    in
        (evalOpM $ Id k) ⊗ p ⊗ (evalOpM $ Id (n-k-1))

-- Auxiliary definitions -- move to internal module?
tol :: RealT
tol = 1e-14

ii, one :: ComplexT
ii  = 0 :+ 1 
one = 1     

zeros :: Int -> Int -> CMat
zeros m n = konst 0 (m,n)

        


-- apply :: Op -> Vector -> Vector -- How do define abstract state instead, for easy backend switching?

realM, imagM :: CMat -> RMat
realM m = cmap realPart m
imagM m = cmap imagPart m

realMI, imagMI :: CMat -> [[Int]]
realMI = map (map (floor.realPart)) . toLists 
imagMI = map (map (floor.imagPart)) . toLists 

{-| sparseMat takes an (m >< n) matrix and returns ((m,n), nonzeros) where nonzeros is a list of every nonzero index paired with the corresponding value. -}
sparseMat :: CMat -> ((Int,Int), [((Int,Int),ComplexT)])
sparseMat mat = 
    let 
        (m,n) = (rows mat, cols mat)
        full_list = case (m,n) of
            (1,1) -> []
            (_,1) -> [((i,0), mat `atIndex` (i,0)) | i <- [0..m-1]]
            (1,_) -> [((0,j), mat `atIndex` (0,j)) | j <- [0..n-1]]
            _     -> error $ show "Use sparseOp for operators"
    in
        ((m,n), filter (\(_,v) -> (magnitude v > tol)) full_list)





