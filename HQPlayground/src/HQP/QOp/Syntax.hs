module HQP.QOp.Syntax where
import Data.Complex
import Data.Word
import Data.Bits(FiniteBits,finiteBitSize,countTrailingZeros,countLeadingZeros,shiftL,shiftR)

type Nat = Int
type RealT = Double  -- Can be replaced by e.g. exact fractions or constructive reals
type ComplexT = Complex RealT

{-|
    The Op type is a symbolic unitary operator, which just builds an abstract syntax tree (AST).
    It provides building blocks for building any n-qubit unitary operator. Explanation of constructors is given below.
 -}  
data QOp 
  = Id Nat -- Identity n: C^{2^n} -> C^{2^n} is the n-qubit identity operator.
                 -- Identity 0: C^1 -> C^1 scalar multiplication by 1, unit for ⊗. 
                 -- Identity 1 = I: C^2 -> C^2
                 -- Identity n is the family of units for ∘.                 
  | Phase Rational -- Global phase e^{i π θ} (scalar multiplication)
  | X | Y | Z | H | SX
  | R QOp Rational  -- Rotation around (possibly multi-qubit) axis defined by QOp by angle (in units of π)
  | C QOp           -- Controlled (possibly multi-qubit) operator
  | Permute [Int]                                                                 
  | Tensor QOp QOp 
  | DirectSum QOp QOp       
  | Compose QOp QOp                        
  | Adjoint QOp 
  deriving (Show,Eq)

{- Quantum programs including measurement. -}
data Step
  = Unitary QOp             -- A unitary quantum program
  | Initialize [Nat] [Bool] -- Initialize qubits qs to classical values vs.
  | Measure    [Nat] -- Measurement of qubits ks (stochastic non-reversible process)
  deriving (Show, Eq)

type Program = [Step]

-- | Syntactic sugar patterns
pattern AtQubit :: QOp -> Nat -> QOp
pattern AtQubit op n <- Tensor (Id n) op
  where AtQubit op n  = Tensor (Id n) op

pattern One, I :: QOp
pattern One <- Id 0
  where One  = Id 0

pattern I <- Id 1
  where I  = Id 1


{-| The Operator type class allows us to work with both the Op symbolic operators, and concrete semantics (e.g. matrices, tensor networks, stabilizers) using the same syntax. I.e., no matter which representation we're working with, we can use the same code to compose, tensor, take adjoints, etc.

The operators form a Semigroup under composition, so we inherit Haskell's standard composition operator <>. Note that a<>b means "first apply b, then a".
-} 
class (Semigroup o, HasTensorProduct o, HasDirectSum o, HasAdjoint o) => Operator o where
  -- Compose is semigroup operator <> with synonym ∘ for math order and >: for left-to-right.
  -- Direct sum: UTF ⊕, ASCII <+> 
  -- Tensor product: UTF ⊗, ASCII <.>

  -- Syntactic sugar in Unicode and ASCII
  (∘),(>:) :: o -> o -> o
  (∘)   = (<>)         -- right-to-left composition (math operator order)
  (>:) a b = b ∘ a   -- left-to-right composition


{-| We define a HilbertSpace typeclass, which we will use for states.
    Tensor product, direct sum, adjoint, and composition are inherited from Operator. 
 -}
class (Scalar v ~ Complex (Realnum v), Floating (Realnum v), HasTensorProduct v) 
    => HilbertSpace v where
  type Realnum v 
  type Scalar  v 

  (.*)  :: Scalar v -> v -> v -- Scalar-vector multiplication
  (.+)  :: v -> v -> v        -- Vector-vector addition
  
  inner :: v -> v -> Scalar v -- Inner product 
  norm  :: v -> Realnum v     -- Vector 2-norm  
  norm a = sqrt(realPart $ inner a a)  

class HasTensorProduct o where
  (⊗) :: o -> o -> o

  (<.>) :: o -> o -> o
  (<.>) = (⊗)

class HasDirectSum o where
  (⊕) :: o -> o -> o

  (<+>) :: o -> o -> o
  (<+>) = (⊕)

class HasAdjoint o where
  adj :: o -> o

instance Semigroup QOp where
  (<>) = Compose

instance HasTensorProduct QOp where (⊗) = Tensor
instance HasDirectSum QOp     where (⊕) = DirectSum
instance HasAdjoint QOp       where adj = Adjoint
instance Operator QOp


infixr 8 ⊗, <.>
infixr 7 ⊕, <+>
infixr 6 ∘, >:

(@>) :: QOp -> Nat -> QOp
(@>) op n = Tensor op (Id n)
(<@) n op = AtQubit op n
(<@) :: Nat -> QOp -> QOp

infixr 5 @>, <@

