module Main where 

import HQP.QOp
import HQP.QOp.MatrixSemantics
import HQP.PrettyPrint

state1q :: ComplexT -> ComplexT -> StateT
state1q a b = a .* ket [0] + b .* ket [1]

{-|
  Clones the full state of a 1-qubit state |ψ> into a 2-qubit state |ψψ>
  Not a physically realizable operation due to the No-cloning theorem!
 -}
quantum_cloned_state :: StateT -> StateT 
quantum_cloned_state ψ = ψ ⊗ ψ

cx_cloned_state :: StateT -> StateT 
cx_cloned_state ψ = 
    let 
        ψ0 = ψ ⊗ ket [0]
        cx = evalOp $ C X
    in
        cx <> ψ0


main :: IO()
main = do
-- Show that CX correctly clones |0> and |1>
    putStr $ "-- Can we clone |0> ? --\n" ++
             "Quantum clone |00> = "
    let q00 = quantum_cloned_state $ ket [0]             
    printS $ q00 

    putStr "XOR clone |00>     = "
    let c00 = cx_cloned_state      $ ket [0]    
    printS $ c00 

    putStr $ "\n-- Can we clone |1> ? --\n" ++
             "Quantum clone |11> = "
    let q11 = quantum_cloned_state $ ket [1]            
    printS q11

    putStr "XOR clone |11>     = "
    let c11 = cx_cloned_state      $ ket [1]    
    printS c11 

    -- let psi = sqrt(1/2) .* ket [0]  + sqrt(1/2) .* ket [1]
    --let psi = sqrt(1/4) .* ket [0]  + sqrt(3/4) .* ket [1]
    let psi = sqrt(1/4) .* ket [0]  + sqrt(3/4) .* ket [1]
    
    putStrLn $ "\n-- Can we clone |ψψ> = " ++ (showState psi) ++ "? --"    

    putStr "Quantum clone |ψψ> = "
    let qpsipsi = quantum_cloned_state psi    
    printS qpsipsi

    putStr "XOR clone   CX|ψ0> = "
    let cpsipsi = cx_cloned_state      psi    
    printS cpsipsi

    let mP  = measureProjection    
    let p10    = mP 2 1 0 -- Effect of measuring second qubit to 0
    let p11    = mP 2 1 1 -- Effect of measuring second qubit to 1

    let qpsi0 = normalize $ p10 <> qpsipsi
    let qpsi1 = normalize $ p11 <> qpsipsi

    let cpsi0 = normalize $ p10 <> cpsipsi
    let cpsi1 = normalize $ p11 <> cpsipsi

    let qm0prob = inner qpsipsi qpsi0
    let qm1prob = inner qpsipsi qpsi1
    let cm0prob = inner cpsipsi cpsi0
    let cm1prob = inner cpsipsi cpsi1
    
    putStrLn "\n-- Mesurement probabilities --"
    putStrLn $ "Probability for measuring 0 on second qubit\n" ++
            " - for   |ΨΨ>:  <ΨΨ|IxP0|ΨΨ>         = " ++ (show qm0prob) ++ "\n" ++
            " - for CX|Ψ0>:  <Ψ0|CX^H IxP0 CX|Ψ0> = " ++ (show cm0prob) ++ "\n"             

    putStrLn $ "Probability for measuring 1 on second qubit\n" ++
            " - for   |ΨΨ>:  <ΨΨ|IxP0|ΨΨ>         = " ++ (show qm1prob) ++ "\n" ++
            " - for CX|Ψ0>:  <Ψ0|CX^H IxP1 CX|Ψ0> = " ++ (show cm1prob) ++ "\n" 

    let (p00,p01) = (mP 2 0 0, mP 2 0 1)
    let qp00 = inner qpsi0 (normalize $ p00 <> qpsi0)
    let cp00 = inner cpsi0 (normalize $ p00 <> cpsi0)
    
    putStrLn $ "\nProbability for measuring 0 on qubit 0 after measuring 0 on qubit 1\n" ++
            " - for   |ΨΨ>:  <ΨΨ|P0xP0|ΨΨ>         = " ++ (show qp00) ++ "\n" ++
            " - for CX|Ψ0>:  <Ψ0|CX^H P0 P0 CX|Ψ0> = " ++ (show cp00) ++ "\n"             
    
    let qp10 = inner qpsi0 (normalize $ p01 <> qpsi0)
    let cp10 = inner cpsi0 (normalize $ p01 <> cpsi0)
    
    putStrLn $ "\nProbability for measuring 1 on qubit 0 after measuring 0 on qubit 1\n" ++
            " - for   |ΨΨ>:  <ΨΨ|P0xP0|ΨΨ>         = " ++ (show qp10) ++ "\n" ++
            " - for CX|Ψ0>:  <Ψ0|CX^H P1 P0 CX|Ψ0> = " ++ (show cp10) ++ "\n"             
    
    


        




-- Why does this prove the no-cloning theorem? 
-- Answer: Uniqueness of a linear operator given its effect on basis vectors => There exists no linear operator (and hence no unitary operator) that can clone an arbitrary qubit state.





