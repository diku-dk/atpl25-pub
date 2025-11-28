module HQP.QOp.Simplify where
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions
import Data.Function (fix)

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f = fix (\rec x ->
    let x' = f x
    in if x' == x then x else rec x')

-- | One is the neutral element for Tensor and Compose. This function removes all redundant occurrences of One in a QOp expression. 
cleanOnes :: QOp -> QOp
cleanOnes op = case op of
    -- Simplification rules
    C One               -> One
    R One _             -> One
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

  




