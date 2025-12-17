module HQP.ZX.Syntax where
import Data.Complex
import Algebra.Graph.Undirected


type RealT = Double  -- Can be replaced by e.g. exact fractions or constructive reals
type ComplexT = Complex RealT

data ZXElement
    = H
    | Green RealT
    | Red RealT
    | Input
    | Output
    | I
    deriving (Eq,Show)
data ZXNode = Node Int ZXElement
    deriving (Eq,Show)

instance Ord ZXNode where
    (<=) (Node a _) (Node b _) = a <= b

type ZXDiagram = Graph ZXNode

