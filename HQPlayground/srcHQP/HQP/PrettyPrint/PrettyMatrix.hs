module HQP.PrettyPrint.PrettyMatrix where

import HQP.QOp.Syntax(RealT,ComplexT)
import HQP.QOp.MatrixSemantics(CMat,RMat, sparseMat)
import HQP.QOp.HelperFunctions(toBits', ilog2)
import Numeric.LinearAlgebra
import Data.List (transpose, intercalate)



-- ----- tolerances / helpers -----
tol :: RealT
tol = 1e-9

nearZero :: RealT -> Bool
nearZero x = abs x <= tol

nearOne  :: RealT -> Bool
nearOne x = abs (x - 1) <= tol

nearInt :: RealT -> Maybe Int
nearInt x = let r = round x in if abs (x - fromIntegral r) <= tol then Just r else Nothing

fmtD :: RealT -> String
fmtD x = maybe (show x) show (nearInt x)  -- integers w/o ".0"

showC :: ComplexT -> String
showC c = 
    let (re,im) = (realPart c, imagPart c)
    in case (re,im) of
        (0,0) -> "0"
        (0,_) -> showR im ++ "*iC"
        (_,0) -> showR re
        _     -> show c

showR :: RealT -> String
showR x =
    let 
        r = round x :: Int
    in
        if abs(x - (fromIntegral r)) < tol 
        then show r
        else show x

showState :: CMat -> String
showState mat = 
    let
        ((m,n),nonzeros) = sparseMat mat
        (logm,logn) = (ilog2 m, ilog2 n)
    in
        case (m,n) of 
            (1,1) -> ""
            (_,1) -> intercalate " + " 
                ((map (\((i,_),v) -> (showC v) ++"*(ket " ++(show $ toBits' logm i)++")" )) nonzeros)
            (1,_) -> intercalate "+" 
                ((map (\((_,j),v) -> (showC v) ++"*(bra " ++(show $ toBits' logn j)++")" )) nonzeros)
            _     -> error "use showQOp for operators"



-- ----- factor common magnitude to ints -----
factorCommonMag :: RMat -> Maybe (RealT, [[Int]])
factorCommonMag m =
  let allrows = toLists m
      nz   = filter (not . nearZero) (concat allrows)
  in case nz of
       []     -> Nothing
       (x:xs) ->
         let c  = abs x
             ok = all (\y -> abs (abs y - c) <= tol) xs
         in if ok
              then
                let q y | nearZero y = 0
                        | otherwise  =
                            case nearInt (y / c) of
                              Just k  -> k
                              Nothing -> error "factorCommonMag: non-integer ratio"
                in Just (c, map (map q) allrows)
              else Nothing

-- ----- exact column alignment with minimal padding -----
-- Right-align each column to its max width; join with commas (no spaces).
alignCols :: [[String]] -> [[String]]
alignCols cells =
  let ws = map (maximum . map length) (transpose cells)
      pad w s = replicate (w - length s) ' ' ++ s
  in [ zipWith pad ws r | r <- cells ]

rowToStr :: [String] -> String
rowToStr = intercalate ","   -- no extra spaces around commas

renderBlockInt :: [[Int]] -> [String]
renderBlockInt allrows =
  let aligned = alignCols (map (map show) allrows)
      n = length aligned
  in case aligned of
       []      -> ["[]"]
       (r:rs)  ->
         let first = " [[" ++ rowToStr r ++ "],"
             mids  = [ "  [" ++ rowToStr x ++ "]," | x <- take (n-2) rs ]
             lastL = if null rs
                       then "[[]]"  -- unreachable when (r:rs) non-empty
                       else "  [" ++ rowToStr (last rs) ++ "]]"
         in if n == 1 then ["[[" ++ rowToStr r ++ "]]"]
                      else first : mids ++ [lastL]

renderBlockReal :: [[RealT]] -> [String]
renderBlockReal allrows =
  let aligned = alignCols (map (map fmtD) allrows)
      n = length aligned
  in case aligned of
       []      -> ["[]"]
       (r:rs)  ->
         let first = " [[" ++ rowToStr r ++ "],"
             mids  = [ "  [" ++ rowToStr x ++ "]," | x <- take (n-2) rs ]
             lastL = if n == 1
                       then "[[" ++ rowToStr r ++ "]]"
                       else "  [" ++ rowToStr (last rs) ++ "]]"
         in if n == 1 then ["[[" ++ rowToStr r ++ "]]"]
                      else first : mids ++ [lastL]

-- ----- analyze real/imag submatrices -----
data RBlock = PlainD [[RealT]] | Factored RealT [[Int]]

analyze :: RMat -> Maybe RBlock
analyze m
  | all nearZero (concat (toLists m)) = Nothing
  | otherwise = case factorCommonMag m of
                  Just (c, imat) -> Just (Factored c imat)
                  Nothing        -> Just (PlainD (toLists m))

-- Emit: optional scalar line, then matrix lines.
emit :: Maybe RealT -> [String] -> [String]
emit ms matLines =
  case ms of
    Just c | not (nearOne c) -> (fmtD c ++ " *") : matLines
    _                        -> matLines

-- ----- top-level pretty printer -----
showCMat :: CMat -> String
showCMat mc =
  let mr = cmap realPart mc
      mi = cmap imagPart mc
      rr = analyze mr
      ri = analyze mi

      realLines =
        case rr of
          Nothing                 -> []
          Just (PlainD drows)     -> emit Nothing (renderBlockReal drows)
          Just (Factored c irows) -> emit (Just c) (renderBlockInt    irows)

      imagLines =
        case ri of
          Nothing                 -> []
          Just (PlainD drows)     -> ("+ i *") : renderBlockReal drows
          Just (Factored c irows) ->
            if nearOne c
              then ("+ i *") : renderBlockInt irows
              else [fmtD c ++ " *", "i *"] ++ renderBlockInt irows

      out =
        case (null realLines, null imagLines) of
          (True , True ) -> ["0"]
          (False, True ) -> realLines
          (True , False) -> imagLines
          (False, False) -> realLines ++ [""] ++ imagLines
  in unlines out

printM, printS :: CMat -> IO()
printM = putStrLn . showCMat
printS = putStrLn . showState