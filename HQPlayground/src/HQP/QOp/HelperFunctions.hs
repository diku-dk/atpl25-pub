module HQP.QOp.HelperFunctions where
import HQP.QOp.Syntax
import Data.Bits(FiniteBits,countTrailingZeros,shiftL,shiftR)
import Data.List (sort)


-- | Signature of an operator a: C^{2^m} -> C^{2^n} is (m,n) = (op_domain a, op_range a)
op_qubits :: QOp -> Nat
op_qubits op = case op of
    Id n    -> n
    C a     -> 1 + op_qubits a
    Tensor    a b -> op_qubits a + op_qubits b
    DirectSum a b -> let  
      (w_a, w_b) = (op_qubits a, op_qubits b)
      in 
        if w_a == w_b then 1+w_a 
        else 
          error $ "Direct sum of incompatible operator dimensions: " 
          ++ show w_a ++ " qubits /= " ++ show w_b ++ " qubits."

    Compose   a b -> max (op_qubits a) (op_qubits b)
    Adjoint   a   -> op_qubits a
    Permute   ks  -> length ks 
    _             -> 1 -- 1-qubit gates

op_dimension :: QOp -> Nat
op_dimension op = 1 `shiftL` (op_qubits op)

step_qubits :: Step -> Nat
step_qubits step = case step of 
  Unitary op -> op_qubits op
  Measure ks -> 1 + maximum ks

prog_qubits :: Program -> Nat
prog_qubits program = maximum $ map step_qubits program



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

-- | Integer logarithm base 2 - change to floor{log_2 n} or ceil{log_2 n}.
ilog2 :: (FiniteBits a, Integral a) => a -> Nat
ilog2 = countTrailingZeros


invertPerm :: [Int] -> [Int]
invertPerm ks = map snd $  -- For each index in the output, find its position in the input
    sort [ (k, i) | (i, k) <- zip [0..] ks ]
