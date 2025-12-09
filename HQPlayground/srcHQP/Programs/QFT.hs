module Programs.QFT where
import HQP

-- | Quantum Fourier Transform on n qubits with MSB input and MSB output.
qft :: Int -> QOp
qft n =  qftrev n ∘ Permute [n-1, n-2 .. 0] 

-- | QFT with LSB input and MSB output (reverse order)
qftrev :: Int -> QOp
qftrev 0 = One
qftrev 1 = H
qftrev n = (qftrev (n-1) ⊗ I) ∘ layer n

-- | QFT layer acting on qubit n
layer :: Int -> QOp  -- acts on n qubits; targets last qubit
layer n = let
        phases_at_n = foldr (∘) One [ cRat k n | k <- [1..n-1] ] 
        h_at_n    = (nI (n-1)) ⊗ H
    in 
        phases_at_n ∘ h_at_n

-- | Z-Rotation (relative phase change) by angle 2π/2^k 
rz :: Int -> QOp
rz k = R Z (2*pi / (2**(fromIntegral k)))

-- | controlled Rz(2π/2^(n-k+1)) with control qubit k and target qubit n. 
cRat :: Int -> Int -> QOp
cRat k n = (nI (k-1)) ⊗ C ((nI (n-k-1)) ⊗ rz (n-k+1)) 

-- | Identity operator on n qubits. When n <= 0, returns the One operator (scalar 1 is neutral element for tensor product). This allows us to write very simple code that doesn't need special cases for n<=0.
nI :: Int -> QOp
nI n
  | n <= 0    = One
  | otherwise = foldr (⊗) One (replicate n I)


