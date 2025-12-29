module Main where

import HQP
import HQP.QOp.MatrixSemantics as MS
import System.Random(mkStdGen, randoms)
import Numeric.LinearAlgebra
import Programs.RepeaterProtocol(repeater, teleport)


-- | Extend a program to act on k additional qubits 
extendprogram ::  Int -> Program -> Program  
extendprogram new_n prog = map extendop prog
  where
    extendop (Unitary u) = let 
        n = op_qubits u
        d = new_n - n
     in Unitary (u ⊗ Id d)
    extendop (Measure ms) = Measure ms

main :: IO()
main = do    
    let rng0 = randoms (mkStdGen 42) :: [Double]    

    let m = 1  -- number of message qubits to teleport
        l = 2  -- number of links between source and target nodes
        n = 2*l -- total chain qubits        
    
    -- | m-qubit quantum state to teleport 
    let 
        {-| Very secret message consisting of 2^m complex amplitudes.
            We use 1,2,...,2^m as an example message, we can transmit
            any m-qubit quantum state. -}
        a i = 2*i 
        b i = 2*i + 1
        t l = b (l-1)

        message' = ((2^m) >< 1) [c :+ 0 | c <- [1..2^m]] :: CMat         
        norm = (sqrt . norm_2) message' :+ 0
        message = (1 / norm) .* message'  -- normalize the message state

        prog = extendprogram (n+m) $ foldr (++) [] [
                repeater l ++ 
                teleport (n+m) (n+i) (a 0) (t l) 
                | i <- [0..m-1] ]            
        


    putStr $ "|ψ_m> = "++(showState message) ++ "\n"
    putStr $ "\nRepeater + Teleportation program:\n" ++ showProgram prog ++ "\n\n"

    putStr $ "\nProgram qubits: " ++ show (map step_qubits prog) ++ "\n\n"

    let psi_chain = ket (replicate n 0) :: CMat  -- initial all-zero state for Bell-chain qubits
        psi = psi_chain ⊗ message -- initial all-zero state and teleport message

    putStr $ "|ψ_0 ⊗ ψ_m> = "++(showState psi) ++ "\nRunning repeater + teleportation program!\n"
    putStr $ "State qubits: " ++ show (ilog2 (rows psi)) ++ "\n\n"

    let (end_state,outcomes,_) = evalProg prog psi rng0

    putStr $ "Measurement outcomes: " ++ (show outcomes) ++"\n";    
    putStr $ "Final " ++ show n ++ "-qubit state:\n" ++ (showState $ norm .* end_state) ++ "\n\n"