module HQP.QOp.HelperFunctions where
import HQP.QOp.Syntax
import Data.Bits(FiniteBits,finiteBitSize,countLeadingZeros,countTrailingZeros,shiftL,shiftR)
import Data.List (sort)
import qualified Data.Set as S


-- | Signature of an operator a: C^{2^m} -> C^{2^n} is (m,n) = (op_domain a, op_range a)


op_dimension :: QOp -> Nat
op_dimension op = 1 `shiftL` (op_qubits op)

step_qubits :: Step -> Nat
step_qubits step = case step of 
  Unitary op -> op_qubits op
  Measure ks      -> 1 + foldr max 0 ks
  Initialize ks _ -> 1 + foldr max 0 ks

           
prog_qubits :: Program -> Nat
prog_qubits program = maximum $ map step_qubits program

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
  Tensor a b    -> (op_support a) `union` ((op_support b) `shift` (op_qubits a))
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

-- | Infinite list of powers of two, constructed with O(1) time per element
powersOfTwo :: [Nat]
powersOfTwo = iterate (*2) 1

dotlists :: Num a => [a] -> [a] -> a
dotlists xs ys = sum $ zipWith (*) xs ys

bitIndexMSB, bitIndexLSB :: [Int] -> Nat
bitIndexMSB ks = dotlists (reverse ks) powersOfTwo
bitIndexLSB ks = dotlists ks powersOfTwo


-- | ilog2 m = floor (log2 m) for m >= 0
ilog2 :: (FiniteBits a, Integral a) => a -> Nat
ilog2 m = finiteBitSize m - countLeadingZeros m - 1

pow2 :: Nat -> Nat
pow2 n = 1 `shiftL` n

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
