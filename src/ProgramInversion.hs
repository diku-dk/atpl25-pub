module ProgramInversion where

import HQP
import Data.List (elemIndex)
import Data.Maybe (fromJust)

{-| 
   In src/Programs/QFT.hs we have implemented the Quantum Fourier Transform (QFT) as a quantum program. First have a look at the QFT implementation there.

   In this exercise, we will get comfortable working with programs as data structures that we can manipulate symbolically, performing program transformations that preserve their semantics.

   1. First generate the QFT program on 1,2, and 3 qubits, and inspect it using both show and the pretty printer. 
   
   2. Evaluate the QFT program on 1, 2, 4, 10 qubits using the matrix semantics from MatrixSemantics.hs. Verify that the resulting matrices are unitary. What would happen if you tried this with 20 qubits? Use 'cabal repl ProgramInversion' to explore this interactively.

   Look in src/HQP/QOp/Simplify.hs for an example of a program transformation that simplifies QOp syntax trees by removing Empty operators. You can use the fixEmpty function from there to simplify your QFT programs before printing or evaluating them. Check that the simplification preserves the semantics of the program.

   3. Now write a function (QOp -> QOp) that performs the inversion of a quantum program. I.e., given Adjoint (qft n), this rewrite function should actually perform the Adjoint operation recursively on all sub-operators, resulting in a new QOp that is the inverse of the original QFT program. 

   To achieve this: 1) Find out what the adjoints of primitive operators I, X, Y, X, Rz(Phi) are.  Can they be expressed as operators in our operator language?  2) What are the rules for what the adjoints of compositions, tensor products, direct sums and permutations are?  
    
   Every operator term in our operator language has an equivalent operator term without any occurrences of the  Adjoint constructor.

    4. Use this function to construct the inverse QFT program by applying it to the QFT program on n qubits. Verify that the inverse QFT program is indeed the inverse by evaluating the composition of QFT and its inverse on some test states.

    5. Write a function that takes a list of rewrite rules (e.g. [cleanEmpty,cleanAdjoint]) and applies them all to a QOp. Then write a function that applies such a list of rewrite rules repeatedly until a fixpoint is reached (i.e., applying the rules does not change the QOp anymore). You can use this to combine multiple optimization passes in your future work.
 -}

adjoint :: QOp -> QOp
adjoint One = One
adjoint I = I
adjoint (Ket b) = Bra b
adjoint X = X
adjoint Y = Y
adjoint Z = Z
adjoint H = H
adjoint SX = X <> SX
adjoint (R op theta) = R (adjoint op) (-theta)
adjoint (C op) = C $ adjoint op
adjoint (Permute l) = Permute l'
   where l' = (\i -> fromJust $ elemIndex i l) <$> [0..(length l - 1)]
adjoint (Compose a b) = Compose (adjoint b) (adjoint a)
adjoint (DirectSum a b) = DirectSum (adjoint a) (adjoint b)
adjoint (Tensor a b) = Tensor (adjoint a) (adjoint b)
adjoint (Adjoint a) = a

cleanAdjoint :: QOp -> QOp
cleanAdjoint (Adjoint a) = adjoint a
cleanAdjoint (Tensor  a b) = Tensor (cleanAdjoint a) (cleanAdjoint b)
cleanAdjoint (DirectSum a b) = DirectSum (cleanAdjoint a) (cleanAdjoint b)
cleanAdjoint (Compose a b) = Compose (cleanAdjoint a) (cleanAdjoint b)
cleanAdjoint (C a) = C $ cleanAdjoint a
cleanAdjoint (R a phi) = R (cleanAdjoint a) phi
cleanAdjoint x = x

applyRewrites :: [QOp -> QOp] -> QOp -> QOp
applyRewrites rewrites op = foldl (flip ($)) op rewrites

-- fixRewrites :: [QOp -> QOp] -> QOp -> QOp
-- fixRewrites rewrites = fixpoint (applyRewrites rewrites)
