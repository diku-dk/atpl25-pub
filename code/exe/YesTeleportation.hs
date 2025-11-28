module Main where 

import HQP
import HQP.QOp.MatrixSemantics
import System.Random(mkStdGen, randoms)
-- import Data.List(intercalate)

teleprog :: Program
teleprog = let
        op1 = Unitary $ 
            (C X) ⊗ I  -:-
            H ⊗ I ⊗ I
        
        op2 = Unitary $ 
            C (I ⊗ Z)  -:-
            I ⊗ (C X)
    in
        [op1, Measure [0,1], op2]

teleport :: StateT -> RNG -> (StateT, RNG)
teleport psi rng  = let
        bell     = sqrt(1/2) .* (ket [0,0] + ket [1,1])
        psi_bell = psi ⊗ bell
    in
        evalProg teleprog psi_bell rng



main :: IO()
main = do
    let rng0 = randoms (mkStdGen 42) :: [Double]    
    --let rng0 = [0,0,0] -- (always measure 0)
    -- let rng0 = [0,1,0] -- (First meausure 0, then measure 1)
    
    let psi = sqrt(1/3) .* ket [0] + sqrt(2/3) .* ket [1]
        bell     = sqrt(1/2)*(ket [0,0] + ket [1,1])
        psi_bell = psi ⊗ bell

    putStr $ "\nTeleport program:\n" ++ showProgram teleprog ++ "\n\n"

--    let path = [False, True,False]
--    let steps = [ fst $ evalStepOp 3 path step| step <- teleprog ]
--    putStr $ "Teleport program matrix semantics:\n" ++ (intercalate "\n" (map showCMat steps)) ++ "\n\n"

    putStr $ "|ψ>   = "++(showState psi) ++ "\n" -- ". Running teleport program!\n"
    putStr $ "|ψbb> = "++(showState psi_bell)++".\nRunning teleport program!\n"

    let (end_state,_) = teleport psi rng0

    putStr $ "Final 3-qubit state:\n" ++ (showState end_state) ++ "\n\n"

    

    
