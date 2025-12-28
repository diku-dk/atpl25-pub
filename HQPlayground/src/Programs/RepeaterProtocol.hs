module Programs.RepeaterProtocol (repeater, teleport) where
import HQP


{-
================================================================================
Entanglement Swapping via a Bell-pair repeater Protocol
================================================================================

The purpose of this protocol is to convert a chain of local Bell pairs into a single
long-distance Bell pair, using only Clifford unitaries and projective
measurements. 

The central step is entanglement swapping via Bell measurements:

 |Φ+>_{a,b} ⊗ |Φ+>_{c,d}  -->  Bell-measurement on (b,c) + CX/CZ correction --> |Φ+>_{a,d}

The details of how this works are given at the end of this file.

No quantum information is transmitted. Instead, entanglement is rewired
by measurement. It is implemented using 4 steps:

  1. Create Local Bell pairs |Φ>_{a_i b_i} between qubits a_i and b_i at neighboring nodes.
  2. Transform into Bell basis for measuring intermediate qubit pairs.
  2. Bell measurements at middle nodes consume local entanglement and swap entanglement to the endpoints.
  3. Apply Pauli corrections at the endpoints, controlled by measurement outcomes.

The output Bell pair can later be used as a communication resource (e.g.
teleportation), but the protocol itself carries no payload and no data.
Creating multiple remote Bell pairs allows for later multi-qubit teleportation.

All operations are Clifford; all non-unitarity is explicit measurement.

Long-form explanation is given at the end of this file, below the code.
-}
-- The main function is:
-- | repeater L
--   1+2) Unitary  U_pre  = (∏_{i=1}^{L-1} (H_{b_{i-1}} ∘ CX_{b_{i-1}→a_i}))
--                        ∘ (∏_{i=0}^{L-1} (CX_{a_i→b_i} ∘ H_{a_i}))
--   3) Measure  M      = [b_0..b_{L-2}] ++ [a_1..a_{L-1}]
--   4) Unitary  U_corr = ∏_{i=1}^{L-1} (CX_{a_i→t} ∘ CZ_{b_{i-1}→t})
bellAt        n a b     = cxAt n a b ∘ hAt n a
bellTransform n b1 a2 = hAt n b1 ∘ cxAt n b1 a2

repeater :: Int -> Program
repeater l
  | l < 1     = []
  | otherwise =
      let n = 2*l
          u_link i = bellAt        n (a i) (b i)                      -- Create chain of Bell pairs
          u_swap i = bellTransform n (b (i-1)) (a i)  -- Setup for Bell measurement that swaps entanglement ab, cd  -->  ad
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

{-
Bell measurement transfers entanglement |Φ>_{AB}, |Φ>_{CD}  -->  |Φ>_{AD}
---------------------------------------------------------------------

Transform between Z-basis and Bell-basis: define the unitary

  U_Bell := (H ⊗ I) · CX_{1→2},
  U_Bell† = CX_{1→2} · (H ⊗ I).

Using

  CX |x,y> = |x, y xor x>,
  H |b>    = (1/√2) ∑_x (-1)^(b x) |x>,

we compute, for b,c ∈ {0,1},

  U_Bell† |b,c>
    = CX (H ⊗ I) |b,c>
    = (1/√2) ∑_x (-1)^(b x) CX |x,c>
    = (1/√2) ∑_x (-1)^(b x) |x, c xor x>
    = (1/√2) ∑_x (-1)^(b x) (I ⊗ X^c) |x, x>
    = (1/√2) (I ⊗ X^c Z^b) (|00> + |11>)
    = (I ⊗ X^c Z^b) |Φ+>

Thus U_Bell maps the Bell basis to the Z basis, and Z-measurement outcomes (b,c)
label the Bell state by the Pauli operator Z^b X^c.

Entanglement swapping with explicit CX/CZ corrections
-----------------------------------------------------

Start with two Bell pairs

  |Ψ0> = |Φ+>_{AB} ⊗ |Φ+>_{CD}.

Apply U_Bell to qubits (B,C) and measure them in the Z basis, obtaining (b,c).
The post-measurement state is (up to normalization)

  I_A ⊗ |b>_B ⊗ |c>_C ⊗ (X_D^c Z_D^b) |Φ+>_{AD}.      (1)

Apply post-measurement corrections using the measured qubits as controls:

  CZ_{B→D} ∘ CX_{C→D}.

Since B and C are in computational basis states,

  CZ_{B→D} = Z_D^b,
  CX_{C→D} = X_D^c.

Applying these to (1) yields

  |b>_B ⊗ |c>_C ⊗ |Φ+>_{AD},

because X^(2c) = Z^(2b) = I.

Thus a Bell measurement on (B,C), followed by controlled-Z from B and
controlled-X from C, deterministically swaps entanglement:

  |Φ+>_{AB} ⊗ |Φ+>_{CD}  →  |Φ+>_{AD}.


--------------------------------------------------------------------------------
Detailed Description of the Repeater Protocol
--------------------------------------------------------------------------------

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

