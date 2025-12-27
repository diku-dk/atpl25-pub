module Main where

import HQP
import HQP.QOp.MatrixSemantics as MS
import System.Random(mkStdGen, randoms)
import Program.RepeaterProtocol(repeater, teleport)

-- | Extend a program to act on k additional qubits 
extendprogram :: Program -> Int -> Program
extendprogram prog k = map extendop prog
  where
    extendop (Unitary u) = Unitary (u ⊗ Id k)
    extendop (Measure ms) = Measure ms

main :: IO()
main = do    
    let rng0 = randoms (mkStdGen 42) :: [Double]    

    let m = 4  -- number of message qubits to teleport
        l = 3  -- number of links between source and target nodes
        n = 2*l -- total chain qubits        
    
    -- | m-qubit quantum state to teleport 
    let 
        {-| Very secret message consisting of 2^m complex amplitudes.
            We use 1,2,...,2^m as an example message, we can transmit
            any m-qubit quantum state. -}
        message' = (2^m >< 1) [1..2^m] :: CMat 
        message = message' / (norm_2 message')

        prog = foldr (++) [] $ [
                extendprogram (repeater l) m ++ 
                teleport (n+4) (n+i) (a 0) (t l) | i <- [1..4]
            ]            

    putStr $ "|ψ> = "++(showState message) ++ "\n"
    putStr $ "\nRepeater + Teleportation program:\n" ++ showProgram prog ++ "\n\n"

    let psi = ket (replicate n 0) ⊗ message -- initial all-zero state and teleport message

    putStr $ "|ψ> = "++(showState psi) ++ "\nRunning repeater + teleportation program!\n"

    let (end_state,outcomes,_) = evalProg prog psi rng0

    putStr $ "Measurement outcomes: " ++ (show outcomes) ++"\n";
    putStr $ "Final " ++ show n ++ "-qubit state:\n" ++ (showState end_state) ++ "\n\n"