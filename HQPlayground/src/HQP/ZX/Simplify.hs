module HQP.ZX.Simplify where
import HQP.ZX.Syntax
import HQP.ZX.Utils
import Algebra.Graph.Undirected
import Data.List

mergeReds :: ZXDiagram -> ZXDiagram
mergeReds g =
    let redSpiders = filter isRed $ vertexList g
    in mergeRedsRec redSpiders g

mergeRedsRec :: [ZXNode] -> ZXDiagram -> ZXDiagram
mergeRedsRec [] g = g
mergeRedsRec (redSpider:redSpiders) g =
    case partition (\ x -> hasEdge redSpider x g) redSpiders of
        ([],nonAdjacentReds) -> mergeRedsRec nonAdjacentReds g
        (redNeighbors,nonAdjacentReds) ->
            let verticesToMerge = redSpider : redNeighbors
                newPhase = sum $ map (getPhase . getElement) verticesToMerge
                (Node nid _) = redSpider
                newSpider = Node nid (Red newPhase)
                newGraph = removeEdge newSpider newSpider $ mergeVertices (`elem` verticesToMerge) newSpider g
            in mergeRedsRec (newSpider:nonAdjacentReds) newGraph
