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
                (Node v _) = redSpider
                newSpider = Node v (Red (newPhase))
                newGraph = removeEdge newSpider newSpider $ mergeVertices (\x -> x `elem` verticesToMerge) newSpider g
            in mergeRedsRec (newSpider:nonAdjacentReds) newGraph

-- Same as merge red spiders?? Special case with only two neighbors for each Hadamard.
-- hadamardRule :: ZXDiagram -> ZXDiagram



-- If a spider has a majority of Hadamard gates on its legs, change its color??
-- changeColorOnMajority :: ZXDiagram -> ZXDiagram


-- If a spider has phase 0 and two legs, it can be removed. - What about multiple legs?
-- remove0PhaseSpiders :: ZXDiagram -> ZXDiagram