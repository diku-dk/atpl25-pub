module Main where

import HQP
import HQP.QOp.MatrixSemantics as MS
import System.Random(mkStdGen, randoms)
import Numeric.LinearAlgebra
import Programs.RepeaterProtocol
import Data.List (partition)



main :: IO()
main = do    
    let rng0 = randoms (mkStdGen 42) :: [Double]    
    -- let rng0 = [0.9,0.9..]

    let m = 3  -- number of message qubits to teleport
        l = 0  -- number of links between source and target nodes
        n = 3*m+2*l
    
    let message_qubits =                [0..m-1] -- m message qubits
        source_qubits  = map (+m)       [0..m-1] -- m source_qubits
        chain_qubits   = map (+2*m)     [0..2*l-1] -- 2*l internal chain qubits
        target_qubits  = map (+2*(m+l)) [0..m-1] -- m target qubits


    putStrLn $ "n = " ++ show n
    -- | m-qubit quantum state to teleport 
    let         
        {-| Very secret message consisting of 2^m complex amplitudes.
            We use 1,2,...,2^m as an example message, we can transmit
            any m-qubit quantum state. -}
        message' = ((2^m) >< 1) [c :+ 0 | c <- [0,1..2^m-1]] :: CMat         
        norm    = norm_2 message' :+ 0
        message = (1 / norm) .* message'  -- normalize the message state
        --message = ket (replicate m 0)   -- <- if we want to look at the bell states un-mangled with the message.
        
        repeater_prog = multiqubitRepeater n source_qubits  chain_qubits target_qubits
        teleport_prog = multiqubitTeleport n message_qubits source_qubits target_qubits
        prog = repeater_prog ++ teleport_prog
        
        
    putStr $ "|ψ_m> = "++(showState message) ++ "\n"
    putStr $ "\nRepeater + Teleportation program:\n" ++ showProgram prog ++ "\n\n"

    putStr $ "\nProgram qubits: " ++ show (map step_qubits prog) ++ "\n\n"

    let psi_chain = ket (replicate (2*m+2*l) 0) :: CMat  -- initial all-zero state for Bell-chain qubits
        psi = message ⊗ psi_chain  -- initial all-zero state and teleport message

    putStr $ "|ψ_0 ⊗ ψ_m> = "++(showState psi) ++ "\nRunning repeater + teleportation program!\n"
    putStr $ "State qubits: " ++ show (ilog2 (rows psi)) ++ "\n\n"
    putStr $ "State norm: " ++ show (norm_2 psi) ++ "\n\n"

    let (end_state,outcomes,_) = evalProg prog psi rng0

    putStr $ "Measurement outcomes: " ++ (show outcomes) ++"\n";    
    putStr $ "Final " ++ show n ++ "-qubit state:\n" ++ (showState $ norm .* end_state) ++ "\n\n"