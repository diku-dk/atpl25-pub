module HQP.ZX.Syntax where
import Data.Complex
import Algebra.Graph.Undirected


type RealT = Double  -- Can be replaced by e.g. exact fractions or constructive reals
type ComplexT = Complex RealT

data Phase = Real RealT | PiHalves Int
    deriving (Eq,Show)

instance Num Phase where
    (+) (Real a) (Real b) = Real $ a+b -- Optionally add mod 2pi to all real cases?? May loose even more precision?
    (+) (PiHalves a) (Real b) = Real $ (fromIntegral a)*pi/2+b
    (+) (Real a) (PiHalves b) = Real $ a+(fromIntegral b)*pi/2
    (+) (PiHalves a) (PiHalves b) = PiHalves $ a+b `mod` 4
    (*) (Real a) (Real b) = Real $ a*b 
    (*) (PiHalves a) (Real b) = Real $ (fromIntegral a)*pi/2*b
    (*) (Real a) (PiHalves b) = Real $ a*(fromIntegral b)*pi/2
    (*) (PiHalves a) (PiHalves b) = PiHalves $ a*b `mod` 4
    abs (Real a) = Real $ abs a
    abs (PiHalves a) = PiHalves $ abs a
    signum (Real a) = Real $ signum a
    signum (PiHalves a) = PiHalves $ signum a
    fromInteger a = (Real $ fromInteger a)
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

