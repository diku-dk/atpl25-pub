module HQP.QOp.Simplify where
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions
import Data.Function (fix)

-- | One is the neutral element for Tensor and Compose. This function removes all redundant occurrences of One in a QOp expression. 
cleanOnes :: QOp -> QOp
cleanOnes op = case op of
    -- Simplification rules
    Id n | n <= 0 -> One
    Phase 0       -> Id 0
    C (Id n)      -> Id (n+1)
    R (Id n) _    -> Id n -- TODO: Include phases: C and <+> can make them relative
    Tensor    (Id m) (Id n) -> Id (m+n)
    Tensor (Tensor a (Id m)) (Id n) -> Tensor a (Id (m+n)) -- Associate Identities to the right
    Tensor (Id m) (Tensor (Id n) b) -> Tensor (Id (m+n)) b -- Associate Identities to the left
    DirectSum (Id m) (Id n) | m == n -> Id (m+1)

    Tensor  One b       -> cleanOnes b
    Tensor  a     One   -> cleanOnes a
    Compose (Id _) b    -> cleanOnes b
    Compose a     (Id _)-> cleanOnes a

    -- Hidden identities
    Permute ks | ks == [0..length ks -1] -> Id (length ks) -- Identity permutation
    R a 0        -> Id (op_qubits a)
    -- Below we just recurse. 
    Tensor  a b           -> Tensor    (cleanOnes a) (cleanOnes b)
    DirectSum a b         -> DirectSum (cleanOnes a) (cleanOnes b)
    Compose a b           -> Compose   (cleanOnes a) (cleanOnes b)
    Adjoint a             -> Adjoint   (cleanOnes a)
    C a                   -> C         (cleanOnes a)
    R a phi               -> R         (cleanOnes a) phi
    -- Rest of constructors are atomsø
    _                     -> op


cleanAdjoints :: QOp -> QOp
cleanAdjoints op = case op of
    Adjoint (Id n)            -> Id n
    Adjoint X                 -> X
    Adjoint Y                 -> Y
    Adjoint Z                 -> Z
    Adjoint H                 -> H
    Adjoint (Phase theta)     -> Phase (-theta)
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

applyPermutation :: [Int] -> [Int] -> [Int]
applyPermutation p q = [ p !! i | i <- q ]

doComp a b = case (a,b) of
    (Id _, x) -> ([],x)
    (x, Id _) -> ([],x)
    (X, X) -> ([],I)
    (Y, Y) -> ([],I)
    (Z, Z) -> ([],I)
    (H, H) -> ([],I)
    (Tensor (Id m) c, Tensor (Id n ) d) | m == n -> 
        let (xs,e) = doComp c d in (map (\x -> Tensor (Id m) x) xs, Tensor (Id m) e)
    (Tensor c (Id m), Tensor d (Id n)) | m == n -> 
        let (xs,e) = doComp c d in (map (\x -> Tensor x (Id m)) xs, Tensor e (Id m))
    (R c theta1, R d theta2) | c == d -> ([],R c (theta1 + theta2))
    (C c, C d) -> let
                    (xs,e) = doComp c d
                 in
                    (map C xs, C e)
    
    (Permute ms, Permute ns) -> ([],Permute (applyPermutation ns ms))   
    _ -> ([a],b)
 

assocComposes :: QOp -> [QOp]
assocComposes (Compose a b) = assocComposes a ++ assocComposes b
assocComposes op          = [op]

assocTensors :: QOp -> [QOp]
assocTensors (Tensor a b) = assocTensors a ++ assocTensors b
assocTensors op          = [op]

composeList :: [QOp] -> [QOp]
composeList (a:b:rest) = let (xs,c) = doComp a b in xs ++ composeList (c:rest)
composeList xs       = xs


doComposes :: QOp -> QOp
doComposes op = case op of
    Compose a b -> foldr1 Compose (composeList (assocComposes a ++ assocComposes b))
    Tensor    a b     -> Tensor    (doComposes a) (doComposes b)
    DirectSum a b     -> DirectSum (doComposes a) (doComposes b)
    Adjoint a         -> Adjoint   (doComposes a)
    C a               -> C         (doComposes a)
    R a phi           -> R         (doComposes a) phi
    _                 -> op

pushComposes :: QOp -> QOp
pushComposes op = let push = pushComposes in case op of
    -- Push compositions down over tensors:
    Compose (Tensor a b) (Tensor c d) -> (push a ∘ push c) ⊗ (push b ∘ push d)
    -- Push compositions down over direct sums:
    Compose (DirectSum a b) (DirectSum c d) -> (push a ∘ push c) <+> (push b ∘ push d)

    -- Recurse
    Tensor    op1 op2     -> (push op1)  ⊗  (push op2)
    DirectSum op1 op2     -> (push op1) <+> (push op2)
    Compose op1 op2       -> (push op1)  ∘  (push op2)
    Adjoint op1           -> Adjoint (push op1)
    _               -> op
    
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
                        (lift a ⊗ id_c) ∘ (lift b ⊗ id_c) ∘ (id_a ⊗ lift c)

{-|
   [A  0] = [A  0] ∘ [I  0] 
   [0 BC]   [0  B]   [0  C] -}    
    DirectSum a (Compose b c)  -> (lift a <+> lift b) ∘ ((Id (op_qubits a)) <+> lift c)
{-|
   [AB 0] = [A 0] ∘ [B 0]
   [0  C]   [0 I]   [0 C] -}
    DirectSum (Compose a b) c -> (lift a <+> (Id (op_qubits c))) ∘ (lift b <+> lift c)


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




