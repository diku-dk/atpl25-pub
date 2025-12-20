module HQP.ZX.Convert where
import qualified HQP.QOp.Syntax as QOp
import HQP.ZX.Syntax
import HQP.ZX.Counter
import Algebra.Graph.Undirected
import HQP.ZX.Utils
-- Convert from QOp to ZXOp
-- TODO add numbers
convert :: QOp.QOp -> ZXDiagram
convert op =
    let (diagram,_) = runCounter (fromQOp op) 0
    in diagram



fromQOp :: QOp.QOp -> Counter ZXDiagram
fromQOp op = case op of
    QOp.Z           -> wrap (Green (PiHalves 2))
    QOp.X           -> wrap (Red (PiHalves 2))
    QOp.R QOp.Z a   -> wrap (Green (Real a))
    QOp.R QOp.X a   -> wrap (Red (Real a))
    QOp.H           -> wrap H
    QOp.C QOp.X     -> do c1 <- generateVertexId
                          c2 <- generateVertexId
                          c3 <- generateVertexId
                          c4 <- generateVertexId
                          c5 <- generateVertexId
                          c6 <- generateVertexId
                          return $ edges [(Node c1 Input,Node c3 (Green 0))
                                         ,(Node c2 Input,Node c4 (Red 0))
                                         ,(Node c3 (Green 0),Node c4 (Red 0))
                                         ,(Node c3 (Green 0),Node c5 Output)
                                         ,(Node c4 (Red 0),Node c6 Output)]
    QOp.Tensor a b -> do g <- fromQOp a
                         g' <- fromQOp b
                         return $  overlay g g'
    QOp.Compose a b -> do g <- fromQOp a
                          g' <- fromQOp b
                          return $ compose g g'
    QOp.Adjoint _ -> error "Remove adjoints before converting to ZX."
    _               -> error "Conversion from QOp to ZXOp not implemented for this constructor."



wrap :: ZXElement -> Counter ZXDiagram
wrap e = do c1 <- generateVertexId
            c2 <- generateVertexId
            c3 <- generateVertexId
            return $ edges [(Node c1 Input,Node c2 e),(Node c2 e,Node c3 e)]


-- connect outputs from a to inputs of b
-- such that x -> Output 1, Input 1 -> y
-- gives x -> y
compose :: ZXDiagram -> ZXDiagram -> ZXDiagram
compose a b =
    let g = overlay a b
        inputs = filter isInput $ vertexList g
        outputs = filter isOutput $ vertexList g
    in foldr mergeAndRemoveIOVertices g (zip inputs outputs)

mergeAndRemoveIOVertices :: (ZXNode,ZXNode) -> ZXDiagram -> ZXDiagram
mergeAndRemoveIOVertices (i,o) g =
    case (getNeighbors i g, getNeighbors o g) of
       ([iN],[oN]) -> overlay (edge iN oN) . removeVertex o . removeVertex i $ g
       _       -> error "Inputs and Outputs can only have 1 edge."
