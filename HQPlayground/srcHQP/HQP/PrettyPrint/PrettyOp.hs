module HQP.PrettyPrint.PrettyOp where
import HQP.QOp.Syntax
import Data.List (intercalate)

showOp :: QOp -> String
showOp op = case op of
    C a             -> "C ("++ showOp a ++ ")"
    a `Tensor`    b -> "(" ++ showOp a ++ " ⊗ " ++ showOp b ++ ")"
    a `DirectSum` b -> "(" ++ showOp a ++ " ⊕ "  ++ showOp b ++ ")"
    a `Compose`   b -> "(" ++ showOp a ++ " <> " ++ showOp b ++ ")"
    Adjoint a       -> "(adj " ++ showOp a ++ ")"
    Bra ks          -> "Bra " ++ show ks -- PatternSynonym Alias for Adjoint (Ket ks)
    _               -> show op

showStep :: Step -> String
showStep (Measure ks) = "Measure " ++ show ks
showStep (Unitary op) = "Unitary $ " ++ showOp op

showProgram :: Program -> String
showProgram steps = intercalate "\n" [ "step" ++ show i ++ " = " ++ (showStep step)
                     | (i :: Int,step) <- zip [1..] steps
                    ]

printOp :: QOp -> IO ()
printOp = putStrLn . showOp