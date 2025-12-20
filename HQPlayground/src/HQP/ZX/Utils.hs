module HQP.ZX.Utils where
import HQP.ZX.Syntax
import Algebra.Graph.Undirected
import Data.List

-- Folds a graph by applying a function to each vertex accumulating a new graph.
foldv :: (ZXNode -> ZXDiagram -> ZXDiagram) -> ZXDiagram -> ZXDiagram
foldv f g = recurse (vertexList g) g 
  where
    recurse [] g' = g'
    recurse (v:vs) g' = recurse vs (f v g')

-- Gets the neighbors of a node in a graph
getNeighbors :: ZXNode -> ZXDiagram -> [ZXNode]
getNeighbors n g =
    let al = adjacencyList g
        res = find (\ (n',_)-> n==n') al
    in case res of
        Nothing -> []
        Just (_,ns) -> ns

isSpider :: ZXNode -> Bool
isSpider (Node _ v) = case v of
    Green _ -> True
    Red _   -> True
    _       -> False

isRed :: ZXNode -> Bool
isRed (Node _ v) = case v of
                Red _ -> True
                _ -> False

asRed :: ZXNode -> Maybe (Int, Phase)
asRed (Node nid (Red p)) = Just (nid, p)
asRed _ = Nothing

isGreen :: ZXNode -> Bool
isGreen (Node _ v) = case v of
                Green _ -> True
                _ -> False

asGreen :: ZXNode -> Maybe (Int, Phase)
asGreen (Node nid (Green p)) = Just (nid, p)
asGreen _ = Nothing

asPhase :: ZXNode -> Maybe Phase
asPhase node =
    case getElement node of
        Green p -> Just p
        Red p   -> Just p
        _       -> Nothing

isInput :: ZXNode -> Bool
isInput (Node _ v) = case v of
                Input -> True
                _ -> False

isOutput :: ZXNode -> Bool
isOutput (Node _ v) = case v of
                Output -> True
                _ -> False

getElement :: ZXNode -> ZXElement
getElement (Node _ e) = e

getVertexId :: ZXNode -> Int
getVertexId (Node v _) = v
