{-# OPTIONS_GHC -Wno-orphans #-}
module Eval where

import Gates
import LinAlg
import qualified Data.Vector as V
import Macros

type PureTensor = V.Vector Qubit

type Tensor = [PureTensor]

instance ApproxEq PureTensor where
  approxEq tolerence a b = V.and $ V.zipWith (approxEq tolerence) a b

instance ApproxEq Tensor where
  approxEq tolerence a b = and $ zipWith (approxEq tolerence) a b

-- |0..0> in tensor notation
zero :: Int -> Tensor
zero dim = [V.replicate dim (qubit 1 0)]

hadamard :: Int -> Tensor
hadamard dim = evalProgram (pow H dim) (zero dim)

-- apply all gates in a program sequentiall (via fold)
evalProgram :: Program -> Tensor -> Tensor
evalProgram program tensor = foldl (flip evalGate) tensor program

-- distributes a gate over addition to all pure tensors in a tensor
evalGate :: Gate -> Tensor -> Tensor
evalGate gate = fixpoint tensorSimp . concatMap (evalTerm gate)

-- evaluates a gate on a pure tensor, using LinAlg Module
evalTerm :: Gate -> PureTensor -> Tensor
evalTerm (Only pos gate) qbs = pure $ qbs V.// [(pos, evalSingle gate (qbs V.! pos))]
evalTerm (Ctrl ctrls target gate) qbs = [qbs, correction]
  where
    beta = product $ [qsnd (qbs V.! i) | i <- ctrls]
    targetVal' = beta *^ (evalSingle gate (qbs V.! target) - (qbs V.! target))
    correction = qbs V.// ((target, targetVal') : zip ctrls (repeat (qubit 0 1)))

tensorSimp :: Tensor -> Tensor
tensorSimp tensor = f tensor [(pureTensorSimp (tensor !! i) (tensor !! j), i, j) | i <- [0..size - 1], j <- [i+1..size-1]]
  where
    size = length tensor
    f :: Tensor -> [(Maybe PureTensor, Int, Int)] -> Tensor
    f t [] = t
    f t (update : updates) =
      case update of
        (Nothing, _, _) -> f t updates
        (Just pt', i, j) -> pt' : deleteAtTwo (i, j) t

pureTensorSimp :: PureTensor -> PureTensor -> Maybe PureTensor
pureTensorSimp t1 t2 =
  let isEq = V.zipWith (~=) t1 t2
  in case countFalse isEq of
      0 ->
        let lastIndex = length t1 - 1
        in Just $ t1 V.// [(lastIndex, 2 *^ (t1 V.! lastIndex))]
      1 -> do
        firstFalseIndex <- V.findIndex not isEq
        Just $ t1 V.// [(firstFalseIndex, (t1 V.! firstFalseIndex) + (t2 V.! firstFalseIndex))]
      _ -> Nothing

-- Utility Functions

countFalse :: V.Vector Bool -> Int
countFalse = V.length . V.filter not

fixpoint :: ApproxEq a => (a -> a) -> a -> a
fixpoint f x =
    let x' = f x
    in if x' ~= x then x else f x'

deleteAtTwo :: (Int, Int) -> [a] -> [a]
deleteAtTwo (i, j) xs = [x | (k, x) <- zip [0..] xs, k /= i, k /= j]

-- pretty print

pp :: Tensor -> IO ()
pp [] = putStrLn ""
pp [pt] = putStrLn $ ppPT pt
pp (pt: pt' : pts) = do
  putStr $ ppPT pt
  putStrLn "+"
  pp (pt' : pts)

ppPT :: PureTensor -> String
ppPT pt = V.foldl1 (\acc str -> acc ++ "⊗" ++ str) $ V.map show pt

--
evalByParts :: Int -> Program -> Tensor -> IO Tensor
evalByParts _ [] t = pure t
evalByParts n prog t = do
    let prog1 = take n prog
    let t' = evalProgram prog1 t
    putStrLn $ show (length t') ++ ","
    pp t'
    evalByParts n (drop n prog) t'