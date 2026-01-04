# ATPL/HQP Haskell Framework v3

## A few updates from v2 to Syntax.hs:

0. The program Step data type now includes Initialize:
   ```haskell
   data Step
   = Unitary QOp             -- A unitary quantum program
   | Initialize [Int] [Bool] -- Initialize qubits qs to classical values vs.
   | Measure    [Int]        -- Projective measurement of qubits qs
   ```
   
   Initialize can be implemented by measuring and correcting; but in particular for ZX calculus backends, you want to have Initialize as a distinct operation.

   The unitary operator QOp syntax is:
   ```haskell
    data QOp 
    = Id Int -- Identity n: C^{2^n} -> C^{2^n} is the n-qubit identity operator.
           -- Identity 0: C^1 -> C^1 scalar multiplication by 1, unit for ⊗. 
           -- Identity 1 = I: C^2 -> C^2
           -- Identity n is the family of units for ∘.                 
    | Phase Rational -- Global phase e^{i π θ} (scalar multiplication)
    | X | Y | Z | H | SX
    | R QOp Rational  -- Rotation around (possibly multi-qubit) axis defined by QOp by angle (in units of π)
    | C QOp           -- Controlled (possibly multi-qubit) operator
    | Permute [Int]     -- k-qubit operator (k=length qs) with wire reordering of the k qubits.
    | Tensor    QOp QOp -- (m+n)-qubit tensor product A ⊗ B if A,B are m-qubit resp. n-qubit operators
    | DirectSum QOp QOp -- Unitary branching: A <+> B = |0><0|A + |1><1|B = 'if q0 then A else B'
    | Compose   QOp QOp -- Sequential composition A ∘ B (first apply B, then A)
    | Adjoint QOp 
   ```
   with changes detailed below. Qubit numbers in Permute are relative, e.g.
   ```haskell
      Id 2 ⊗ Permute [2,0,1] ≡ Permute [0,1,4,2,3]
   ```
   Thus no reordering is needed when combined through tensor products, direct sums, or control. 

1. Angles are now Rational numbers given in units of π. E.g. R Z θ = e^{-iπθ/2}|0><0| + e^{iπθ/2}|1><1|. 
   This makes it much easier to read QOp expressions.

2. Replaced 'One' (0-qubit identity, neutral element for ⊗) by more general Phase θ (scalar multiplication by e^{iθπ}).
   One = Phase 0 is a 'pattern' rule instead of its own constructor. Pattern rules can still be used both as constructors and in pattern matching rules.

   While the v2 QOp definition was complete (every n-qubit unitary could be specified), Phase θ is needed for many transformation rules in e.g. Stabilizer algebra and ZX algebra implementations.

   Note that while global phases are not measurable, a global phase e^{iθπ}A becomes relative when controlled:

    C (e^{iθπ} A) = (R Z θ ⊗ I) ∘ C A

 3. Identity gate I is replaced by the more general n-qubit identity 'Id n'. This makes it much easier to 1) construct
    operators that act on specific qubits (instead of repeated I⊗I⊗ ⋯ ⊗I), and 2) to recognize on which qubits operators act nontrivially, and 3) avoids a lot of clutter in the QOp representations. This makes implementing ZX and Stabilizers easier, as well as programming quantum algorithms.

    Example:

    atQubit n k g = Id k ⊗ g ⊗ Id (n-k-1) -- Produces the n-qubit operator with 1-qubit gate g acting on qubit k.

    Some syntactic shorthand for qubit placement have been added: 

   ```haskell
      k <@ op    = Id k ⊗ op         -- place at qubit k
         op @> l = op ⊗ Id l         -- extend to l additional qubits
      k <@ op @> l = Id k ⊗ op Id l  -- (k+l+1)-qubit operator that acts on qubit k
   ```
 
 4. To make it easy to work with your semantics backends using the same syntax as for QOp, we define a number of 
    traits-typeclasses HasX that you can use if your semantics data type implements them:

   ```haskell
   class HasTensorProduct o where
      (<.>) :: o -> o -> o -- ASCII infix tensor product operator
      (⊗)   :: o -> o -> o -- Unicode synonym      
      (⊗) = (<.>) 

   class HasDirectSum o where
      (<+>) :: o -> o -> o -- ASCII direct sum infix operator
      (⊕)   :: o -> o -> o -- Unicode synonym
      (⊕) = (<+>) -- 

   class HasAdjoint o where adj :: o -> o
   class HasQubits  o where n_qubits :: o -> Nat
   
   ```
   This makes it possible to write code that works with different backends without modification. However, not all backends support all operations - e.g. Stabilizers don't support direct sum or linear combinations.
   
   To equip your data type with these operations, write something like:

   ```haskell
   instance HasTensorProduct QOp where (⊗) = Tensor
   instance HasDirectSum QOp     where (⊕) = DirectSum
   instance HasAdjoint QOp       where adj = Adjoint
   instance HasQubits  QOp       where n_qubits = op_qubits
   instance Semigroup QOp where (<>) = Compose
   instance Operator QOp
   ```

## Change to the semantics backend interface: 

evalOp is unchanged, but the evalStep and evalProg are updated to include measurement outcomes. In summary, a semantics backend must define:

```haskell
type StateT = ... -- Representation of states, e.g. vector, stabilizer tableau, tensors, ...
type OpT    = ... -- Representation of operators, e.g. matrix, haskell function StateT -> StateT, ...
evalStep :: (StateT, Outcomes, RNG) -> Step -> (StateT, Outcomes, RNG)
```
where 
```haskell
type Outcomes = [Bool]   -- Outcomes in stack order (latest measurement is head of list)
type RNG      = [Double] -- Random number generator (just an indinite list of numbers 0..1)
```

This makes program evaluation a simple fold of evalStep over the program:
```haskell
evalProg :: Program -> StateT -> RNG -> (StateT, Outcomes, RNG)
evalProg steps psi0 rng0 = foldl evalStep (psi0, [], rng0) steps
```
See ```MatrixSemantics.hs``` for an example implemenation of evalStep. You own backend can use the same implementation almost verbatim: you just need to define 

```haskell
evalOp   :: QOp -> OpT                                                -- A ↦ [[A]]
measure1 :: (StateT, Outcomes, RNG) -> Nat -> (StateT, Outcomes, RNG) -- measure single qubit and prepend to outcomes
apply :: OpT -> StateT -> StateT                                      -- (A,ψ) ↦ [[A ψ]]
ket   :: [Int] -> StateT                                              -- Build basis state: [a1,...,an] ↦ |a1,...,an>
```
Note that evalOp does not need to evaluate to a full representation of the operator, if your semantics backend data type does not easily allow that. It's totally fine to just build a lambda (i.e. delayed evaluation), so long as you can
later apply it to a ```StateT``` using ```apply```.

## RepeaterProtocol.hs: New application program for testing Clifford backends

In order to benchmark and test Stabilizer implementations, I've written a quantum communication program that can generate useful workloads consisting only of Clifford operations, and which can scale to arbitrarily large numbers of qubits and operations. 

The program implements the Repeater Protocol, which, given a sequence of qubits located as pair-wise neighbours, linking a sender and receiver, sets up Bell pairs that allow for later teleporting full quantum states directly from sender to receiver. 

```src/Programs/RepeaterProtocol.hs``` implements this, both for constructing the remote Bell pair (split between sender and receiver) and subsequent teleportation. Functions for both single qubit transmission and for multi-qubit transmission are exported. 

```exe/TestRepeater.hs``` is a test of multi-qubit repeater protocol and multi-qubit teleportation, transmitting a length-2^m message, using amplitudes of 0,1,2,...,2^m-1 (normalized) as a simple example. You can test it currently using the (very slow!) MatrixSemantics backend, and plug in your Stabilizer backend or ZX backend to verify correctness and benchmark.

