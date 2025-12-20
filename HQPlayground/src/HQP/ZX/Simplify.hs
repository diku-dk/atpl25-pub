module HQP.ZX.Simplify where
import HQP.ZX.Syntax
import HQP.ZX.Utils
import Algebra.Graph.Undirected
import Data.Maybe (mapMaybe)

-- If red spiders are connected, they can be merged into a single spider with phase equal to the sum of the phases.
mergeRedSpiders :: ZXDiagram -> ZXDiagram
mergeRedSpiders graph = foldv helper graph
  where
    helper node graph'
        | Just (nid, nPhase) <- asRed node
        = let (nids, phases) = unzip $ (nid, nPhase) : mapMaybe asRed (getNeighbors node graph')
              newSpider = Node nid (Red $ sum phases)
              newGraph = mergeVertices ((`elem` nids) . getVertexId) newSpider graph'
          in removeEdge newSpider newSpider newGraph
        | otherwise = graph'

-- If a spider has phase 0 and two legs, it can be removed.
removeSimpleSpiders :: ZXDiagram -> ZXDiagram
removeSimpleSpiders graph = foldv helper graph
  where
    helper node graph'
        | Just 0 <- asPhase node
        , neighbor : ns <- getNeighbors node graph'
        , length ns <= 1
        = replaceVertex node neighbor $ removeEdge node neighbor graph'
        | otherwise = graph'

-- Same as merge red spiders?? Special case with only two neighbors for each Hadamard.
-- hadamardRule :: ZXDiagram -> ZXDiagram

-- If a spider has a majority of Hadamard gates on its legs, change its color??
-- changeColorOnMajority :: ZXDiagram -> ZXDiagram
