module HQP.QOp.HelperFunctions where
import HQP.QOp.Syntax
import Data.Bits(FiniteBits,countTrailingZeros)


-- | Signature of an operator a: C^{2^m} -> C^{2^n} is (m,n) = (op_domain a, op_range a)
op_range :: QOp -> Int
op_range op = case op of
    One          -> 0
    Ket ks        -> length ks 
    C a           -> 1 + op_range a
    Tensor    a b -> op_range a + op_range b
    DirectSum a b -> let 
      (w_a, w_b) = (op_range a, op_range b)
      in 
        if w_a == w_b then 1+w_a 
        else 
          error $ "Direct sum of incompatible operator dimensions: " 
          ++ show w_a ++ " qubits /= " ++ show w_b ++ " qubits."

    Compose   a b -> max (op_range a) (op_range b)
    Adjoint   a   -> op_domain a
    Permute   ks  -> length ks 
    _             -> 1 -- 1-qubit gates


op_domain :: QOp -> Int
op_domain op = case op of
    One          -> 0
    Ket _        -> 0 
    C a           -> 1 + op_domain a
    Tensor    a b -> op_domain a + op_domain b
    DirectSum a b -> let 
      (w_a, w_b) = (op_domain a, op_domain b)
      in 
        if w_a == w_b then 1+w_a 
        else 
          error $ "Direct sum of incompatible operator dimensions: " 
          ++ show w_a ++ " qubits /= " ++ show w_b ++ " qubits."
    Compose   a b -> max (op_domain a) (op_domain b)
    Adjoint   a   -> op_range a
    Permute   ks  -> length ks 
    _             -> 1 -- 1-qubit gates

step_range :: Step -> Int
step_range step = case step of 
  Unitary op -> op_range op
  Measure ks -> 1 + maximum ks

prog_range :: Program -> Int
prog_range program = maximum $ map step_range program



-- Small helper functions
toBits :: (Integral a) => a -> [a]
toBits 0 = []
toBits k = (toBits (k `div` 2)) ++ [(k `mod` 2)]

toBits' :: Int -> Int -> [Int]
toBits' n k = let 
    bits = toBits k
    m    = length bits
  in
    (replicate (n-m) 0) ++ bits

ilog2 :: (FiniteBits a, Integral a) => a -> Int
ilog2 = countTrailingZeros
