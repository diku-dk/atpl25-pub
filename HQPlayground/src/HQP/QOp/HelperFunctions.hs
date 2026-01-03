module HQP.QOp.HelperFunctions where
import HQP.QOp.Syntax
import Data.Bits(FiniteBits,finiteBitSize,countLeadingZeros,countTrailingZeros,shiftL,shiftR)
import Data.List (sort)
import qualified Data.Set as S


op_dimension :: QOp -> Nat
op_dimension op = 1 `shiftL` (n_qubits op)


-- | Support of an operator: the list of qubits it acts non-trivially on.
op_support :: QOp -> S.Set Nat
op_support op = let
    shift ns k   = S.map (+k) ns
    union xs ys  = S.union xs ys
    permute_support     π sup = S.fromList [ i | (i,j) <- zip [0..] π, S.member j sup ]
    permute_support_inv π sup = S.fromList [ j | (i,j) <- zip [0..] π, S.member i sup ]
  in case op of
  Id _          -> S.empty
  Phase _       -> S.empty
  R _ 0         -> S.empty
  R a _         -> op_support a
  C a           -> S.insert 0 ((op_support a) `shift` 1)
  Tensor a b    -> (op_support a) `union` ((op_support b) `shift` (n_qubits a))
  DirectSum a b -> S.insert 0 ((op_support a `union` op_support b) `shift` 1)
  Compose (Permute ks) b -> permute_support ks (op_support b)
  Compose a (Permute ks) -> permute_support_inv ks (op_support a)
  Compose a b   -> union (op_support a) (op_support b)
  Adjoint a     -> op_support a
  Permute ks    -> S.fromList $ permSupport ks
  _             -> S.singleton 0 -- 1-qubit gates


-- Small helper functions
toBits :: (Integral a) => a -> [a]
toBits 0 = []
toBits k = (toBits (k `div` 2)) ++ [(k `mod` 2)]

toBits' :: Nat -> Nat -> [Nat]
toBits' n k = let 
    bits = toBits k
    m    = length bits
  in
    (replicate (n-m) 0) ++ bits

-- | ilog2 m = floor (log2 m) for m >= 0
ilog2 :: (FiniteBits a, Integral a) => a -> Nat
ilog2 m = finiteBitSize m - countLeadingZeros m - 1

evenOdd :: [a] -> ([a],[a])
evenOdd [] = ([],[])
evenOdd [x] = ([x],[])
evenOdd (x:y:xs) = let (es,os) = evenOdd xs in (x:es,y:os)

permApply :: [Int] -> [a] -> [a]
permApply ks xs = [ xs !! k | k <- ks ]

permSupport :: [Int] -> [Int]
permSupport ks = [ i | (i,j) <- zip [0..] ks, i /= j ]

invertPerm :: [Int] -> [Int] -- TODO: invertPerm -> permInvert for consistency
invertPerm ks = map snd $  -- For each index in the output, find its position in the input
    sort [ (k, i) | (i, k) <- zip [0..] ks ]
