module HQP.ZX.Syntax where
import Data.Complex
import Algebra.Graph.Undirected
import Data.Fixed (mod')


type RealT = Double  -- Can be replaced by e.g. exact fractions or constructive reals
type ComplexT = Complex RealT

data Phase = Real RealT | PiHalves Int
    deriving (Show)

tolerance :: Fractional a => a
tolerance = 1e-3

instance Eq Phase where
    (Real a) == (Real b) = abs (a - b) `mod'` (2*pi) < tolerance
    (PiHalves a) == (Real b) = abs (fromIntegral a * pi / 2 - b) `mod'` (2*pi) < tolerance
    (Real a) == (PiHalves b) = abs (a - fromIntegral b * pi / 2) `mod'` (2*pi) < tolerance
    (PiHalves a) == (PiHalves b) = (a `mod` 4) == (b `mod` 4)

instance Num Phase where
    (+) (Real a) (Real b) = Real $ (a+b) `mod'` (2*pi)
    (+) (PiHalves a) (Real b) = Real $ (fromIntegral a * pi / 2 + b) `mod'` (2*pi)
    (+) (Real a) (PiHalves b) = Real $ (a + fromIntegral b * pi / 2) `mod'` (2*pi)
    (+) (PiHalves a) (PiHalves b) = PiHalves $ (a+b) `mod` 4
    (*) (Real a) (Real b) = Real $ (a*b) `mod'` (2*pi)
    (*) (PiHalves a) (Real b) = Real $ (fromIntegral a * pi / 2 * b) `mod'` (2*pi)
    (*) (Real a) (PiHalves b) = Real $ (a * fromIntegral b * pi / 2) `mod'` (2*pi)
    (*) (PiHalves a) (PiHalves b) = PiHalves $ (a*b) `mod` 4
    abs (Real a) = Real $ abs a
    abs (PiHalves a) = PiHalves $ abs a
    signum (Real a) = Real $ signum a
    signum (PiHalves a) = PiHalves $ signum a
    fromInteger a = Real $ fromInteger a `mod'` (2*pi)
    negate (Real a) = Real $ negate a
    negate (PiHalves a) = PiHalves $ negate a

data ZXElement
    = H
    | Green Phase
    | Red Phase
    | Input
    | Output
    deriving (Eq,Show)
data ZXNode = Node Int ZXElement
    deriving (Eq,Show)

instance Ord ZXNode where
    (<=) (Node a _) (Node b _) = a <= b

type ZXDiagram = Graph ZXNode

