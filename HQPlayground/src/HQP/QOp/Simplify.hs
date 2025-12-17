module HQP.QOp.Simplify where
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions
import Data.Function (fix)

-- | One is the neutral element for Tensor and Compose. This function removes all redundant occurrences of One in a QOp expression. 
cleanOnes :: QOp -> QOp
cleanOnes op = case op of
    -- Simplification rules
    C (Id n)      -> Id (n+1)
    R (Id n) _    -> Id n -- TODO: Include phases: C and <+> can make them relative
    Tensor (Id m) (Id n) -> Id (m+n)
    DirectSum (Id m) (Id n) | m == n -> Id (m+1)

    Tensor  One b       -> cleanOnes b
    Tensor  a     One   -> cleanOnes a
    Compose One b       -> cleanOnes b
    Compose a     One   -> cleanOnes a
    Compose a     I     -> cleanOnes a
    Compose I     a     -> cleanOnes a
    -- Below we just recurse. 
    Tensor  a b           -> Tensor    (cleanOnes a) (cleanOnes b)
    DirectSum a b         -> DirectSum (cleanOnes a) (cleanOnes b)
    Compose a b           -> Compose   (cleanOnes a) (cleanOnes b)
    Adjoint a             -> Adjoint   (cleanOnes a)
    C a                   -> C         (cleanOnes a)
    R a phi              -> R         (cleanOnes a) phi
    -- Rest of constructors are atomsø
    _                     -> op


cleanAdjoints :: QOp -> QOp
cleanAdjoints op = case op of
    Adjoint (Id n)            -> Id n
    Adjoint X                 -> X
    Adjoint Y                 -> Y
    Adjoint Z                 -> Z
    Adjoint H                 -> H
    Adjoint (R a theta)       -> R (cleanAdjoints a) (-theta)
    Adjoint (C a)             -> C (cleanAdjoints (Adjoint a))
    Adjoint (Adjoint a)       -> cleanAdjoints a
    Adjoint (Permute ks)      -> Permute (invertPerm ks)
    --(AB)^-1 = B^-1 A^-1
    Adjoint (Compose a b)     -> Compose (cleanAdjoints (Adjoint b)) (cleanAdjoints (Adjoint a))
    Adjoint (Tensor a b)      -> Tensor  (cleanAdjoints (Adjoint a)) (cleanAdjoints (Adjoint b))
    Adjoint (DirectSum a b)   -> DirectSum (cleanAdjoints (Adjoint a)) (cleanAdjoints (Adjoint b))
      
      -- No more rewrite rules. Recurse over non-leaf constructors.
    Tensor  a b               -> Tensor    (cleanAdjoints a) (cleanAdjoints b)   
    DirectSum a b             -> DirectSum (cleanAdjoints a) (cleanAdjoints b)
    Compose a b               -> Compose   (cleanAdjoints a) (cleanAdjoints b)
    C a                       -> C         (cleanAdjoints a)
    R a phi                   -> R         (cleanAdjoints a) phi
    _                         -> op    



{-| Tensors and DirectSums are bifunctorial over Composes, i.e.,
      (a ⊗ b) ∘ (c ⊗ d)  =  (a ∘ c) ⊗ (b ∘ d)
      (a ⊕ b) ∘ (c ⊕ d)  =  (a ∘ c) ⊕ (b ∘ d)

    For cases when we have "buried compositions" that do not syntactically exhibit the bifunctorial pattern, we can introduce appropriate identities to lift the compositions to the top level:

    1. a ⊗ (b ∘ c)  =  (a ⊗ I) ∘ (I ⊗ b) ∘ (I ⊗ c) 
    2. (a ∘ b) ⊗ c  =  (a ⊗ I) ∘ (b ⊗ I) ∘ (I ⊗ c) 
    3. a ⊕ (b ∘ c)  =  (a ⊕ I) ∘ (I ⊕ b) ∘ (I ⊕ c)
    4. (a ∘ b) ⊕ c  =  (a ⊕ I) ∘ (b ⊕ I) ∘ (I ⊕ c)

   This function lifts compositions over tensor products and direct sums.
   Note that this operates on QOp, not MOp, since MOp does not have binary Tensors/DirectSums/Composes.
   -}
liftComposes :: QOp -> QOp
liftComposes op = let lift = liftComposes in case op of
    -- | Lift compositions over tensors and direct sums that match the bifunctorial pattern.
    Tensor    (Compose a b) (Compose c d) -> (lift a  ⊗  lift c) ∘ (lift b  ⊗  lift d)
    DirectSum (Compose a b) (Compose c d) -> (lift a <+> lift c) ∘ (lift b <+> lift d)
    
    -- | Introduce identities to lift "buried compositions" using bifunctoriality:
    Tensor a (Compose b c)   ->  let 
                        (na,nb)      = (op_qubits a,  op_qubits b)
                        (id_a, id_b) = (Id na, Id nb) -- Assume nb = nc
                    in
                        (lift a ⊗ lift id_b) ∘ (lift id_a ⊗ lift b) ∘ (lift id_a ⊗ lift c)
    
    Tensor (Compose a b) c   ->  let 
                        (na,nc)      = (op_qubits a,  op_qubits c)
                        (id_a, id_c) = (Id na, Id nc) 
                    in
                        (lift a ⊗ lift id_c) ∘ (lift b ⊗ lift id_c) ∘ (lift id_a ⊗ lift c)
    
    DirectSum a (Compose b c)   ->  let 
                        (na,nb)      = (op_qubits a,  op_qubits b)
                        (id_a, id_b) = (Id na, Id nb) -- Assume nb = nc
                    in
                        (lift a <+> lift id_b) ∘ (lift id_a <+> lift b) ∘ (lift id_a <+> lift c)
    
    DirectSum a (Compose b c)   ->  let 
                        (na,nc)      = (op_qubits a,  op_qubits c)
                        (id_a, id_c) = (Id na, Id nc) 
                    in
                        (lift a <+> lift id_c) ∘ (lift b <+> lift id_c) ∘ (lift id_a <+> lift c)

    -- | Recurse
    Tensor    op1 op2     -> (lift op1)  ⊗  (lift op2)
    DirectSum op1 op2     -> (lift op1) <+> (lift op2)
    Compose op1 op2       -> (lift op1)  ∘  (lift op2)
    Adjoint op1           -> Adjoint (lift op1)
    _               -> op    


-- | Apply a list of rewrite rules once.
simplifyPass :: [o -> o] -> o -> o
simplifyPass rewriterules op = foldr (\f acc -> f acc) op rewriterules

-- | Fixpoint with a guard to ensure termination after at most n iterations.
fixpoint :: Eq a => Int -> (a -> a) -> a -> a 
fixpoint 0 _ x = x
fixpoint n f x = let 
      fx = f x
   in 
      if fx == x then x else fixpoint (n-1) f fx


-- | Apply a list of rewrite rules repeatedly until a fixpoint is reached, or at most n iterations.
simplifyFixpoint :: Eq o => Int -> [o -> o] -> o -> o
simplifyFixpoint n rewriterules op = fixpoint n (simplifyPass rewriterules) op  




