{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE TypeFamilies              #-}


module CircDiagram where

import Diagrams.Prelude
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.TwoD.Text (Text)

-- Drawing ---------------------------------------------------------------

gateDia :: Gate -> QDiagram B V2 Double Any
gateDia g = ( text lbl # fontSizeL 0.25 <> roundedRect 0.6 0.4 0.08 # lw thin # fc white # opacity 1 ) where lbl = case g of I -> "I"; G s -> s

drawRow :: Row -> QDiagram B V2 Double Any
drawRow gs =  
  let
      nodes = hsep 0.5 (map gateDia gs)       -- remove # centerXY
      line  = hrule (width nodes)
               # alignL                       -- left-align the line
    in  (line # alignL) `beneath` (nodes # alignL)


drawCircuit :: Circuit -> QDiagram B V2 Double Any
drawCircuit = vsep 0.5 . map drawRow

-- Move to test ---

c1, c2, c3 :: Circuit
c1 = [[G "H", G "X"], [G "Z", G "Y",G "X"]]
c2 = [[G "CX"], [G "H", G "H"]]
c3 = [[G "H"], [G "H", G "H", G "H"]]

-- nodestyle :: Diagram B -> Diagram B
-- nodestyle = fontSizeL 0.2 # fc white 

-- node :: Int -> Diagram B
-- node n = text (show n) # nodestyle <> circle 0.2 # named n

-- points  = trailVertices (regPoly 6 1)
-- diagram = atPoints points $ map node [1..6]

-- main = mainWith (pad 1.1 diagram)
