module HQP.QOp.Operator where
import Data.Complex
import Data.Tuple (swap)

type RealT = Double
type ComplexT = Complex RealT
type Nat = Int -- { n : Int | n >= 0 } (refinement type)

-- Single-qubit unitary operators
data QubitOp =  I | X |  Y | Z | H | SX | S | T deriving (Show, Eq)

-- Multi-qubit unitary operators and combinators
data Operator 
  = Atom QubitOp
  | C Operator                                 
  | Permute [Int]                                                                 
  | Tensor Operator Operator 
  | Id Nat                      -- Id n = identity on n qubits
  | Compose Operator Operator   -- Diagrammatic composition                 
  | Adjoint Operator
  deriving (Show,Eq)

-- operator number (of qubits)
num :: Operator -> Nat
num (Atom g) = 1
num (C op) = 1 + num op
num (Permute indices) = length indices
num (Tensor op1 op2) = num op1 + num op2
num (Id n) = n
num (Compose op1 op2) = if n1 == n2 then n1 else error "invalid composition"
   where n1 = num op1
         n2 = num op2
num (Adjoint op) = num op

-- tensor terms: have form sum_{i=1}^r (qi(0) tensor qi(1) tensor ... tensor qi(k-1))
-- denote arbitary elements of H^{tensor k} where H = C^2.  
type Qubit = (ComplexT, ComplexT)
type PureTensor = [Qubit]      -- rank-1 tensor product of qubits
type TensorTerm = [PureTensor] -- sum of pure tensors, must all have same length

ket0, ket1 :: Qubit
ket0 = (1, 0)
ket1 = (0, 1)

i = 0 :+ 1

zero :: TensorTerm
zero = []

add :: TensorTerm -> TensorTerm -> TensorTerm  -- must be of same qubit rank
add t1 t2 = t1 ++ t2

scale :: ComplexT -> TensorTerm -> TensorTerm
scale k ts = map (scale' k) ts

scale' :: ComplexT -> PureTensor -> PureTensor
scale' k [] = error "scale applied to 0 qubits"
scale' k ((a, b) : qs) = (k * a, k * b) : qs

gate :: QubitOp -> Qubit -> Qubit
gate I q = q
gate X (a, b) = (b, a)
gate Y (a, b) = (-i * b, i * a)
gate Z (a, b) = (a, -b)
gate H (a, b) = (nf * (a + b), nf * (a - b)) where nf = 1 / sqrt 2
gate _ _ = undefined

eval :: Operator -> TensorTerm -> TensorTerm
eval (Atom g) ts = map (map (gate g)) ts
eval (C op) ts = map f0 ts -- `add` map (ket1 :) (eval op (map f1 ts))
     where f0 ((a, b) : qs) = ket0 : scale' a qs
           f0 [] = error "Missing qubit..."
           f1 ((a, b) : qs) = scale' b qs
           f1 [] = error "Missing qubit.."
eval (Permute indices) ts = undefined
eval (Tensor op1 op2) ts = concatMap (prod . process . split) ts
  where num1 = num op1
        split = splitAt num1
        process (t1, t2) = (res1 t1, res2 t2)
        res1 t1 = eval op1 [t1]
        res2 t2 = eval op2 [t2]
        prod (ts1, ts2) = [t1 ++ t2 | t1 <- ts1, t2 <- ts2]
eval (Id n) ts = ts
eval (Compose op1 op2) ts =
  if num op1 == num op2
  then eval op2 (eval op1 ts)
  else error "Incompatible number of qubits"
eval (Adjoint op) ts  = eval (normalize (Adjoint op)) ts

-- elimininate Adjoint in operator expressions
normalize op = undefined -- 

