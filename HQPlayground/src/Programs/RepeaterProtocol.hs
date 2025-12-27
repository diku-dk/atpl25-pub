module Programs.RepeaterProtocol (repeater, teleport) where
import HQP


{-
================================================================================
Entanglement Swapping via a Bell-pair repeater Protocol
================================================================================

The purpose of this protocol is to convert many local Bell pairs into a single
long-distance Bell pair, using only Clifford unitaries and projective
measurements.

No quantum information is transmitted. Instead, entanglement is rewired
by measurement. It is implemented using three steps:

  1. Create Local Bell pairs |Φ>_ab between qubits a and b at neighboring nodes.
  2. Transform into Bell basis for measuring intermediate qubit pairs.
  2. Bell measurements at middle nodes consume local entanglement:
      |Φ+>_{a,b} ⊗ |Φ+>_{c,d}  -->  Bell-measurement on (b,c)  -->  |Φ+>_{a,d}
  3. Apply Pauli corrections at the endpoints, controlled by measurement outcomes.

The output Bell pair can later be used as a communication resource (e.g.
teleportation), but the protocol itself carries no payload and no data.
Creating multiple remote Bell pairs allows for later multi-qubit teleportation.

All operations are Clifford; all non-unitarity is explicit measurement.

Long-form explanation is given at the end of this file, below the code.
-}
-- The main function is:
-- | repeater L
--   1) Unitary  U_pre  = (∏_{i=1}^{L-1} (H_{b_{i-1}} ∘ CX_{b_{i-1}→a_i}))
--                     ∘ (∏_{i=0}^{L-1} (CX_{a_i→b_i} ∘ H_{a_i}))
--   2) Measure  M      = [b_0..b_{L-2}] ++ [a_1..a_{L-1}]
--   3) Unitary  U_corr = ∏_{i=1}^{L-1} (CX_{a_i→t} ∘ CZ_{b_{i-1}→t})
bellAt n a b = cxAt n a b ∘ hAt n a

repeater :: Int -> Program
repeater l
  | l < 1     = []
  | otherwise =
      let n = 2*l
          u_link i = bellAt n (a i) (b i)
          u_swap i = hAt n (b (i-1)) ∘ cxAt n (b (i-1)) (a i)
          u_corr i = cxAt n (a i) (t l) ∘ czAt n (b (i-1)) (t l)

          u_pre  = foldr (∘) (Id n) (map u_swap [1..l-1])
                 ∘ foldr (∘) (Id n) (map u_link [0..l-1])

          meas   = [ b i | i <- [0..l-2] ] ++ [ a i | i <- [1..l-1] ]

          u_corr_all = foldr (∘) (Id n) (map u_corr [1..l-1])
      in
        [ Unitary u_pre,
          Measure meas,
         Unitary u_corr_all
        ]

teleport :: Int -> Int -> Int -> Int -> Program
teleport n q source target = -- teleport qubit q using Bell pair (a0,t)
  [ 
    Unitary ( hAt n q ∘ cxAt n q source ),
    Measure [ q, source ],
    Unitary ( cxAt n source target ∘ czAt n q target )
  ]

--------------------------------------------------------------------------------
-- Auxiliary functions
--------------------------------------------------------------------------------
-- layout: a_i = 2i, b_i = 2i+1, total n = 2L, target t = b_{L-1}
a :: Int -> Int
a i = 2*i

b :: Int -> Int
b i = 2*i + 1

t :: Int -> Int
t l = b (l-1)

--------------------------------------------------------------------------------
-- Gate placement
--------------------------------------------------------------------------------
bringToFront :: Int -> [Int] -> [Int]
bringToFront n front = front ++ filter (`notElem` front) [0..n-1]

embed :: Int -> [Int] -> QOp -> QOp
embed n ws u =
  let p   = bringToFront n ws
      k   = length ws
  in (adj $ Permute p) ∘ (u ⊗ Id (n-k)) ∘ Permute p

at1 :: Int -> Int -> QOp -> QOp
at1 n i g = embed n [i] g

at2 :: Int -> Int -> Int -> QOp -> QOp
at2 n i j g = embed n [i,j] g

hAt :: Int -> Int -> QOp
hAt n i = at1 n i H

cxAt :: Int -> Int -> Int -> QOp
cxAt n c x = at2 n c x (C X)

czAt :: Int -> Int -> Int -> QOp
czAt n c z = at2 n c z (C Z)


{-| 
Long-form explanation:

Setup
-----
Fix a chain length L ≥ 1.

For each link i = 0,…,L−1, we have two qubits:
  a_i   -- left endpoint of link i
  b_i   -- right endpoint of link i

The endpoints of the chain are:
  a_0           (left endpoint)
  t := b_{L−1}  (right endpoint)

All measurements are in the computational (Z) basis.

Step 1: Fused preparation unitary U_pre
---------------------------------------
This unitary performs two tasks simultaneously:

  (1) Prepare a Bell pair on each link (a_i, b_i).
  (2) Apply the standard pre-rotations needed to realize Bell measurements
      on each intermediate pair (b_{i−1}, a_i).

For each link i = 0,…,L−1, define
  U_link^(i) := CX_{a_i → b_i} ∘ H_{a_i}

For each intermediate node i = 1,…,L−1, define
  U_swap^(i) := H_{b_{i−1}} ∘ CX_{b_{i−1} → a_i}

The fused preparation unitary is
  U_pre :=
      ( ∏_{i=1}^{L−1} U_swap^(i) )
    ∘ ( ∏_{i=0}^{L−1} U_link^(i) )

This creates Bell pairs on all links and prepares all swap pairs
for Bell measurement in a single Clifford unitary.


Step 2: Measurements M
---------------------------
Measure the 2(L−1) qubits { b_0,…,b_{L−2} } ∪ { a_1,…,a_{L−1} } in the Z basis.

This is equivalent to performing Bell measurements on each pair (b_{i−1}, a_i),  i = 1,…,L−1,
and produces classical outcome bits m_{b_{i−1}}, m_{a_i} ∈ {0,1}.
After this step, all measured qubits are classical.


Step 3: Correction unitary U_corr
---------------------------------------

Because the measured qubits have collapsed to |0⟩ or |1⟩, Pauli corrections can be applied unitarily using them as controls.

For each i = 1,…,L−1, define U_corr^(i) := CX_{a_i → t} ∘ CZ_{b_{i−1} → t}

The fused correction unitary is U_corr := ∏_{i=1}^{L−1} U_corr^(i)

Operationally, this applies the Pauli
  X_t^{ ⊕_i m_{a_i} }  Z_t^{ ⊕_i m_{b_{i−1}} }
to the endpoint t, but without any classical-side Pauli-frame bookkeeping.


Net Effect
----------

Starting from |0⟩^{⊗ 2L}, the three-step program

  U_corr ∘ M ∘ U_pre

deterministically produces the Bell state

  |Φ⁺⟩_{a_0 t} = (|00⟩ + |11⟩) / √2

on the endpoints a_0 and t, with all intermediate qubits measured and discarded.

Thus, the protocol transforms the chain of L short-range Bell pairs into one 
long-range Bell pair using only Clifford operations and measurements.
-}

