module HQP.QOp.Syntax where
import Data.Complex

type RealT = Double  -- Can be replaced by e.g. exact fractions or constructive reals
type ComplexT = Complex RealT

{-|
    The Op type is a symbolic unitary operator, now extended with bra/ket-states, which just builds an abstract syntax tree (AST).
    It provides building blocks for building any n-qubit unitary operator. Explanation of constructors is given below.
 -}  
data QOp 
  = One -- Neutral element for tensor product and composition
  | Ket [Int]        
  | I| X | Y | Z | H | SX 
  | R QOp RealT  
  | C QOp                                 
  | Permute [Int]                                                                 
  | Tensor QOp QOp 
  | DirectSum QOp QOp       
  | Compose QOp QOp                        
  | Adjoint QOp 
  deriving (Show,Eq)

-- | Haskell magic that allows us to use Bra like a constructor without redundancy.
pattern Bra :: [Int] -> QOp
pattern Bra ks <- Adjoint (Ket ks)
  where Bra ks =  Adjoint (Ket ks)



{- Quantum programs including measurement. -}
data Step
  = Unitary QOp    -- A unitary quantum program
  | Measure [Int] -- Measurement of qubits ks (stochastic non-reversible process)
  deriving (Show, Eq)

type Program = [Step]


{-| The Operator type class allows us to work with both the Op symbolic operators, and concrete semantics (e.g. matrices, tensor networks, stabilizers) using the same syntax. I.e., no matter which representation we're working with, we can use the same code to compose, tensor, take adjoints, etc.

The operators form a Semigroup under composition, so we inherit Haskell's standard composition operator <>. Note that a<>b means "first apply b, then a".
-} 
class Semigroup o => Operator o where
  compose    :: o -> o -> o   -- Sequential composition 
  tensorProd :: o -> o -> o   -- Tensor product ⊗
  directSum  :: o -> o -> o   -- Direct sum     ⊕
  adj        :: o -> o        -- Adjoint: Inverse for unitary operators, bra <-> ket for states

  compose = (<>) -- Default semigroup compose operator. Operators form a SG under composition.

  -- Syntactic sugar in Unicode and ASCII
  (∘),(>:), (⊗), (⊕), (<.>), (<+>) :: o -> o -> o
  (∘)   = compose         -- right-to-left composition (math operator order)
  (>:) a b = compose b a -- left-to-right composition
  (⊗)   = tensorProd
  (⊕)   = directSum
  (<.>) = tensorProd 
  (<+>) = directSum  
  

instance Semigroup QOp where
  (<>) = Compose

instance Operator QOp where
  tensorProd = Tensor
  directSum  = DirectSum
  adj        = Adjoint


infixr 8 ⊗, <.>
infixr 7 ⊕, <+>
infixr 6 ∘, >:

{-| Explanation of Op constructors:

    One = Phase 0 is the neutral element for tensor product (0-qubit identity operator, scalar 1).

    Ket [k1,k2,...,kn] :: C -> C^{2^n} is the n-qubit ket |k1 k2 ... kn>, where ki are 0 or 1    
    
    The adjoint Bra [k1,k2,...,kn] :: C^{2^n} -> C is not included in the syntax as a separate constructor, since it can be expressed as Bra ks = Adjoint (Ket ks), to reduce the number of rules needed to manipulate the syntax.

    I | X | SX | Y | Z | H  are standard 1-qubit gates g :: C^2 -> C^2.
    
    R a θ = exp(-i*theta/2 a) :: C^{2^n} -> C^{2^n} with n = op_range a
    is a rotation around the axis defined by op by angle θ. E.g. R Z (pi/2) is a phase gate. Note that this syntax allows rotations around multi-qubit gates, e.g. R (X ⊗ Y) (pi/3). 

    C a = |0><0| ⊗ I^n + |1><1| ⊗ a :: C^{2^{n+1}} -> C^{2^{n+1}} 
    is the controlled version of an operator a, where the first qubit is the control qubit. E.g. C X is the CNOT gate. This also allows for controlled multi-qubit operations, e.g. C (X ⊗ H) = |0><0| ⊗ I + |1><1| ⊗ (X ⊗ H)

    Permute ks is an (length ks)-qubit operator that permutes the order of qubits according to the list ks, e.g.  Permute [2,0,1] on |q0 q1 q2> yields |q2 q0 q1>

    Tensor a b = a ⊗ b is the operator that acts on the ensemble (i.e. entangled) domain of a and b

    DirectSum a b = a ⊕ b acts independently on pairs from the domain of a and b. This is used to model choice, i.e. a ⊕ b = |0><0| ⊗ a + |1><1| ⊗ b. Note that for qubit operators, a and b must have the same dimension.

    Compose a b = a <> b means "first apply b, then a" (sequential composition).

    Adjoint op: inverse for unitaries, Bra <-> Ket for states.

    The syntax is over-complete for ease of expressing programs. E.g. Adjoint Bra ks = Ket ks, C can be expressed using DirectSum, X = Compose H Z H, etc.

    A minimal universal syntax could be (but there are many equivalent choices):
    data Op' = Ket0 | I | SX | Rz RealT 
             | DirectSum Op' Op' | Tensor Op' Op' | Compose Op' Op' | Adjoint Op'
   |-}


{- A pure quantum program on n qubits is a unitary linear operator U: C^{2^n} -> C^{2^n}. 

 We can built any unitary from 1-Q unitaries and a single 1-Q unitary (e.g. CNOT) through tensor products and composition. Tensor product of an m-qubit and an n-qubit unitary yields an m+n-qubit unitary, and omposing two n-qubit unitaries yields another n-qubit unitary. Thus, no matter how many operations a pure quantum program involves, it is still simply a unitary linear operator.

 A general quantum program can include measurement steps. A measurement collapses parts of the   wavefunction to a classical result. Note that even if one measures only a single qubit, it changes the full n-qubit state: it also affects which values *any other entangled qubit can  take*. This is a non-unitary operation: measuring  qubit k to the classical value v acts as a *projection* of the n-qubit state onto the subspace in which qubit k has value v, followed by re-normalization. 
-}

