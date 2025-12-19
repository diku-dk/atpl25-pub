module HQP.ZX.Utils where
import HQP.ZX.Syntax
import Algebra.Graph.Undirected
import Data.List


neighbors :: ZXNode -> ZXDiagram -> [ZXNode]
neighbors n g =
    let al = adjacencyList g
        res = find (\ (n',_)-> n==n') al
    in case res of
        Nothing -> []
        Just (_,ns) -> ns



isRed :: ZXNode -> Bool
isRed (Node _ v) = case v of
                Red _ -> True
                _ -> False

isGreen :: ZXNode -> Bool
isGreen (Node _ v) = case v of
                Green _ -> True
                _ -> False

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


getPhase :: ZXElement -> Phase
getPhase (Green p) = p
getPhase (Red p) = p
getPhase e = error $ "Cannot get phase of element: "++ show e