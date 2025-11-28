module HQP.QOp.Simplify where
import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions
import Data.Function (fix)


fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f = fix (\rec x ->
    let x' = f x
    in if x' == x then x else rec x')

cleanEmpty :: QOp -> QOp
cleanEmpty op = case op of
    C Empty               -> Empty
    C a                   -> C (cleanEmpty a)
    Tensor  Empty b       -> cleanEmpty b
    Tensor  a     Empty   -> cleanEmpty a
    Compose Empty b       -> cleanEmpty b
    Compose a     Empty   -> cleanEmpty a
    Compose a     I      -> cleanEmpty a
    Compose I     a      -> cleanEmpty a
    DirectSum Empty b     -> cleanEmpty b
    DirectSum a     Empty -> cleanEmpty a
    Tensor  a b           -> Tensor    (cleanEmpty a) (cleanEmpty b)
    DirectSum a b         -> DirectSum (cleanEmpty a) (cleanEmpty b)
    Compose a b           -> Compose   (cleanEmpty a) (cleanEmpty b)
    Adjoint a             -> Adjoint   (cleanEmpty a)
    _                     -> op

fixEmpty :: QOp -> QOp
fixEmpty = fixpoint cleanEmpty
  

-- | rectangularize take a general QOp syntax tree and outputs a "rectangular" syntax tree on the form of a list of Compositions of n-qubit tensor products.
--rectangularize :: QOp -> QOp

    

simplifyOp :: QOp -> QOp
simplifyOp op = case op of
    Tensor  (Ket ks) (Ket ls) -> Ket (ks ++ ls)
    Compose a I               -> simplifyOp a
    Compose I a               -> simplifyOp a
    DirectSum a b  -> DirectSum (simplifyOp a) (simplifyOp b)
    Tensor a b   -> Tensor  (simplifyOp a) (simplifyOp b)
    Compose a b  -> Compose (simplifyOp a) (simplifyOp b)
    Adjoint a    -> Adjoint (simplifyOp a)
    _            -> op

adj_pushdown :: QOp -> QOp
adj_pushdown op = case op of
    Adjoint I                 -> I
    Adjoint X                 -> X
    Adjoint Y                 -> Y
    Adjoint Z                 -> Z
    Adjoint H                 -> H
    Adjoint (Adjoint a)       -> adj_pushdown a
    Adjoint (Compose a b)     -> adj_pushdown (Compose (Adjoint b) (Adjoint a))--(AB)^-1 = B^-1 A^-1
    Adjoint (Tensor a b)      -> adj_pushdown (Tensor  (Adjoint a) (Adjoint b))
    Adjoint (DirectSum a b)   -> adj_pushdown (DirectSum (Adjoint a) (Adjoint b))
    -- Compose a (Adjoint a)     -> I -- A^{-1}A = I 
    -- Compose (Adjoint a) a     -> I -- AA^{-1} = I
    Tensor  a b               -> Tensor  (adj_pushdown a) (adj_pushdown b)
    DirectSum a b             -> DirectSum (adj_pushdown a) (adj_pushdown b)
    Compose a b               -> Compose (adj_pushdown a) (adj_pushdown b)
    _                         -> op    






