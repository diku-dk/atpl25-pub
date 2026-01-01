{-# LANGUAGE TypeFamilies #-}

module HQP.QOp.MatrixSemantics where

import HQP.QOp.Syntax
import HQP.QOp.Simplify
import HQP.PrettyPrint.PrettyOp
import HQP.QOp.HelperFunctions
import Numeric.LinearAlgebra hiding(normalize,step,(<>)) -- the hmatrix library
import Data.Bits(shiftL,xor)
import Data.Array(accumArray,elems)
import Data.List(sort)
import Debug.Trace(trace)

type CMat = Matrix ComplexT
type RMat = Matrix RealT
type StateT = CMat
type OpT    = CMat


{-| 
 evalOp :: Op -> CMat
 (evalOp op) evaluates the pure quantum operator op (defined in Circuit.hs) in the matrix semantics, and produces a complex matrix of dimension 2^n x 2^n (where n is the qubit-length of op)
-}
evalOp  :: QOp -> CMat
evalOp op = case op of
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

    SX -> evalOp $ R X (1/2)

    R axis q -> 
        let mat  = evalOp axis
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
                            mop = evalOp op1
                            mI  = ident (rows mop)
                        in
                            mI <+> mop -- |0><0| ⊗ I^n + |1><1| ⊗ op1
    
    Tensor    op1 op2 -> (evalOp op1)  ⊗  (evalOp op2)
    Compose   op1 op2 | (op_qubits op1 == op_qubits op2) -> (evalOp op1)  ∘  (evalOp op2)  
                      | otherwise -> error $ 
                       "\n\nDim-mismatch: " ++ showOp op1 ++ " ∘ " ++ showOp op2 ++ "\n"
    DirectSum op1 op2 | (op_qubits op1 == op_qubits op2) -> (evalOp op1)  <+> (evalOp op2)  
                      | otherwise -> error $ 
                       "\n\nDim-mismatch: " ++ showOp op1 ++ "<+>" ++ showOp op2 ++ "\n"
    Adjoint op1         -> adj $ evalOp op1


--  State contruction: An n-qubit state can be represented by a vector in C^{2^n} (we'll later see potentially more compact representations). 

bra, ket :: [Int] -> CMat

{-| bra [v0,...,v_{n-1}] (where v_j is 0 or 1) is the adjoint state <v0 v1 ... v_{n-1}|. In the matrix representation, this is a row-vector in C^{2^n}, i.e. of dimension (1 >< 2^n). -}
bra []     = (1><1) [1]
bra (v':vs) = let 
        v = fromIntegral v' 
    in 
        (1><2) [1-v,v] ⊗ (bra vs)

{-| ket [v0,...,v_{n-1}] (where v_j is 0 or 1) is the state |v0 v1 ... v_{n-1}>. In the matrix representation, this is a column-vector in C^{2^n}, i.e. of dimension (2^n >< 1). -}
ket vs     = adj $ bra vs


{-| Measurements require random numbers, which are non-deterministic by nature. Everything here is kept purely functional except, with side effects restricted to program mains, so random numbers are simply given as a list of Doubles between 0 and 1. -}
type RNG = [Double]

{-| 'evalStep rng step state' evaluates a computational step (unitary or measurement) given the current state and returns the modified quantum state. 

To deal with random measurements in a pure functional setting, we treat a random number generator rng as an infinite list of numbers between 0 and 1. This allows the library to remain pure - IO comes in from program mains. 

We take a random number generator as the first parameter, read off the first element, and return
the remainder together with the updated quantum state.
-} 
type Outcomes = [Bool] -- Measurement outcomes as list of bits

{-| measure1 measures a single qubit, projecting the state on the subspace corresponding to the 
    outcome, and prepends the outcome to the list of outcomes -}
 
measure1 :: Int -> (StateT, Outcomes, RNG) -> Int -> (StateT, Outcomes, RNG)
measure1 _ (_,_,[]) _ = error "No more random numbers. This never happens."
measure1 n (state, outcomes, (r:rng)) k = let
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


evalStep :: (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
evalStep (state, outcomes, rng) step = -- trace("evalStep "++ show step) $ 
    let n = ilog2 (rows state) in case step of
    Unitary op | (op_qubits op == n) -> ((evalOp op) <> state, outcomes, rng)
               | otherwise -> error $ "Dim-mismatch between " ++ showOp op ++ " and n="++show n

    -- outcomes are latest-first, so ks is reversed on input
    Measure ks -> foldl (measure1 n) (state, outcomes, rng) (reverse ks) 

    Initialize ks vs -> let
        (st,os,rng') = evalStep (state,[],rng) $ Measure ks 

        -- List of outcomes xor values for each initialized qubit
        corrections = zipWith xor os vs
        -- Now we build the full list, including unaffected qubits
    
        corrections_full    = accumArray xor False (0,n-1) (zip ks corrections)
    
        correction_operator = cleanop $ foldl (⊗) One [if c then X else I | c <-elems corrections_full]
        
        (st',os',rng'') = evalStep (st,outcomes,rng') (Unitary correction_operator)
        in
            --trace("vs = " ++ show vs)
            --trace("os = " ++ show os)
            --trace("corrections = " ++ show corrections)
            --trace("correction_operator = " ++ showOp correction_operator)
            --trace("st  = " ++ show st) 
            --trace("st' = " ++ show st') 
            (st',os',rng'')

{-| 'evalProg steps psi0 rng' evaluates a quantum program (a list of steps) on an initial state psi0, using the random number generator rng for measurements. It returns the final state and the remaining RNG. -}
evalProg :: [Step] -> StateT -> RNG -> (StateT, Outcomes, RNG)
evalProg steps psi0 rng  =
  foldl evalStep (psi0, [], rng) steps


{-| We define a HilbertSpace typeclass, which we will use for states.
    Tensor product, direct sum, adjoint, and composition are inherited from Operator. 
 -}
class (Scalar v ~ Complex (Realnum v), Floating (Realnum v)) => HilbertSpace v where
  type Realnum v 
  type Scalar  v 

  (.*)  :: Scalar v -> v -> v -- Scalar-vector multiplication
  (.+)  :: v -> v -> v        -- Vector-vector addition
  
  inner :: v -> v -> Scalar v -- Inner product 
  norm  :: v -> Realnum v     -- Vector 2-norm  
  norm a = sqrt(realPart $ inner a a)  

{-|
 - The tensor product of two operators in matrix representation a :: (m><n) and b :: (p><q) is the kronecker product c :: (m*p >< n*q) with entries c_{i*p+k, j*q+l} = a_{ij}*b_{kl} 

 - The direct sum of two operators in matrix representation a :: (m><n) and b :: (p><q) is the block-diagonal matrix c :: ((m+p) >< (n+q)) with a and b as blocks. Note that the additive dimension necessitates that a and b have the same dimensions for it to be realizable on qubits. 

 - The operator adjoint in matrix representation is the conjugate transpose.
-}    

instance Operator CMat where
    tensorProd = kronecker
    directSum a b = fromBlocks [[a, zeros (rows a) (cols b)],
                                [zeros (rows b) (cols a), b]]
    adj = tr -- HMatrix confusingly defines conjugate transpose as 'tr' (standard trace notation)



{-| We implement ket-states as (n >< 1) matrices (= column vectors), and bra-states as (1 >< n) matrices (= row vectors). Thus StateT inherits the operator operations (recall that states
are also linear operators by Riesz representation), but we can also treat them like vectors,
so we implement the VectorSpace operations. -}
instance HilbertSpace StateT where
    type Scalar  StateT = ComplexT 
    type Realnum StateT = RealT
    
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


{-
evalStepOp :: Int -> [Bool] -> Step -> (CMat, [Bool])
evalStepOp _ [] _ = error "Please provide a path."
evalStepOp n (p:path) step = case step of
    Unitary op -> (evalOp op, p:path) -- TODO: assert n = dim op?
    Measure [] -> (ident (2^n) :: CMat, p:path)
    Measure (k:ks) -> let
            proj_k          = measureProjection n k (if p then 1 else 0)
            (proj_ks,path') = evalStepOp n path (Measure ks)
         in
            (proj_ks <> proj_k, path') 

-}

{-|
 measureProjection n k result 
 
Builds the projection operator onto the subspace of C^{2^n} in which qubit k has value 'result'.
 
Construction of the operator:
I ⨷ ... ⨷ I ⨷ P ⨷ I ⨷ ... ⨷ I 
\-- k-1 --/                   /
 \------------ n ------------/
-}
measureProjection :: Int -> Int -> Int -> CMat
measureProjection n k result = 
    let p = if k==0 
            then
                let v = fromIntegral result :: ComplexT
                in (2><2) [1-v, 0,
                           0,   v]
            else 
                evalOp I
    in
        if n>1 
        then
            p ⊗ (measureProjection (n-1) (k-1) result)
        else 
            p





-- Auxiliary definitions -- move to internal module?
tol :: RealT
tol = 1e-14

ii, one :: ComplexT
ii  = 0 :+ 1 
one = 1     

zeros :: Int -> Int -> CMat
zeros m n = konst 0 (m,n)

normalize :: StateT -> StateT
normalize s = let 
        n = (norm_2 (flatten s))
    in 
        if (n < tol) then s 
        else              s / scalar (n :+ 0)
        


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





