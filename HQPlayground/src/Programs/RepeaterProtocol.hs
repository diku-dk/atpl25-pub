module Programs.RepeaterProtocol (repeater, teleport, multiqubitRepeater,multiqubitTeleport, bellAt) where
import HQP
import Debug.Trace(trace)


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
bellAt, bellTransform :: Int -> Int -> Int -> QOp
bellCorrection :: Int -> Int -> Int -> Int -> QOp
bellAt         n s t     = (cxAt n s t ) ∘ (hAt n s)
bellTransform  n t1 s2   = (hAt n t1   ) ∘ (cxAt n t1 s2)
bellCorrection n t1 s2 t = (cxAt n s2 t) ∘ (czAt n t1 t)


repeater :: Nat -> [Nat] -> [Nat] -> Program
repeater n sources targets | (length sources) == (length targets) =
        let 
          l = length sources -- trace("repeater "++show (n,sources,targets)) 
          u_bells = [bellAt n a b             | (a,b)   <- zip sources targets]
          u_swaps = [bellTransform  n b1 a2   | (a2,b1) <- zip (tail sources) (init targets) ]
          u_corrs = [bellCorrection n b1 a2 t | (a2,b1) <- zip (tail sources) (init targets) ]
            where t = last targets

          u_pre  = foldr (∘) (Id n) u_swaps
                 ∘ foldr (∘) (Id n) u_bells

          -- Measure away everything except endpoints
          meas   = (init targets) ++ (tail sources)

          u_post = foldr (∘) (Id n) u_corrs
      in
        --trace ("repeater " ++ show (n,sources,targets))
        [
          Initialize (sources++targets) (replicate (2*l) False),
          Unitary u_pre,
          Measure meas,
          Unitary u_post,
          Initialize (tail sources ++ init targets) (replicate (2*l-2) False)
        ]
    | otherwise = error $ "length sources " ++ show sources ++ " != length targets " ++ show targets

multiqubitRepeater :: Nat -> [Nat] -> [Nat] -> [Nat] -> Program
multiqubitRepeater n source_qubits chain_qubits target_qubits = let
    (chain_sources,chain_targets) = evenOdd chain_qubits
  in
    --trace ("multiqubitRepeater "++ show (n,source_qubits,chain_qubits,target_qubits) ++ " -> " ++   show (chain_sources,chain_targets))
    foldl (++) [] [
        repeater n (s:chain_sources) (chain_targets++[t]) | (s,t) <- zip source_qubits target_qubits
    ]

teleport :: Nat -> Nat -> Nat -> Nat -> Program
teleport n q source target = let -- teleport qubit q using Bell pair (a0,t)
    prog = [ 
      Unitary $ cleanop ( hAt n q ∘ cxAt n q source ),
      Measure [ q, source ],
      Unitary $ cleanop ( cxAt n source target ∘ czAt n q target ) ]
  in 
    --trace ("\n\nTeleport "++(show (n,q,source,target)++" = "++(showProgram prog++"\n"))) 
    prog

multiqubitTeleport :: Nat -> [Nat] -> [Nat] -> [Nat] -> Program
multiqubitTeleport n message bell_sources bell_targets = let
  u_pre  = foldr (∘) (Id n) $ 
              [hAt n q ∘ cxAt n q s| (q,s) <- zip message bell_sources ] 

  meas   = message ++ bell_sources

  u_post = foldr (∘) (Id n) $
              [cxAt n s t | (s,t) <- zip bell_sources bell_targets] ++ 
              [czAt n q t | (q,t) <- zip message bell_targets]
  in
    [
      Unitary u_pre,
      Measure meas,
      Unitary u_post,
      Initialize message (replicate (length message) False)
    ]

--------------------------------------------------------------------------------
-- Gate placement
--------------------------------------------------------------------------------
hAt :: Int -> Int -> QOp
hAt n i = Id i ⊗ H ⊗ Id (n-i-1)

cAt :: Int -> QOp  -> Int -> Int -> QOp
cAt n op s t = 
  if s < t then
    Id s ⊗ C (Id (t-s-1) ⊗ op) ⊗ Id (n-t-1)
  else    
    hh ∘ Id t ⊗ C (op ⊗ Id (s-t-1)) ⊗ Id (n-s-1) ∘ hh
  where
    hh = hAt n s ∘ hAt n t  

cxAt :: Int -> Int -> Int -> QOp
cxAt n s t = cAt n X s t

czAt :: Int -> Int -> Int -> QOp
czAt n s t = cAt n Z s t

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

Net Effect
----------

Starting from |0⟩^{⊗ 2L}, the three-step program

  U_corr ∘ M ∘ U_pre

deterministically produces the Bell state

  |Φ⁺⟩_{s t} = (|00⟩ + |11⟩) / √2

on the endpoints s and t, with all intermediate qubits measured and discarded.

Thus, the protocol transforms the chain of L short-range Bell pairs into one 
long-range Bell pair using only Clifford operations and measurements.

Multi-qubit set-up and teleportation is done by repeating the single-qubit repeater protocol.
-}

