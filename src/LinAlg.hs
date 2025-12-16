{-# LANGUAGE DerivingStrategies #-}
module LinAlg(Qubit, qubit, evalSingle, (*^), qfst, qsnd) where

import Gates
import Numeric.LinearAlgebra

newtype Qubit = Qubit (Vector (Complex Double))
  deriving newtype (Show, Num)

qubit :: Complex Double -> Complex Double -> Qubit
qubit a b = Qubit (2 |> [a, b])

(*^) :: Complex Double -> Qubit -> Qubit
z *^ (Qubit v) = Qubit $ scale z v

qfst :: Qubit -> Complex Double
qfst (Qubit v) = v ! 0

qsnd :: Qubit -> Complex Double
qsnd (Qubit v) = v ! 1

ii :: Complex Double
ii = 0 :+ 1

-- toVector :: Qubit -> Vector (Complex Double)
-- toVector (Qubit a b) = 2 |> [a, b]

-- toQubit :: Vector (Complex Double) -> Qubit
-- toQubit v = Qubit (v ! 0) (v ! 1)

evalSingle  :: SingleGate -> Qubit -> Qubit
evalSingle gate (Qubit qb) = Qubit $ mat #> qb
  where
    mat = case gate of
      I -> (2 >< 2) [1,0,
                    0,1]

      X -> (2 >< 2) [0,1,
                    1,0]

      Y -> (2 >< 2) [-ii, 0,
                      0, ii]

      Z -> (2 >< 2) [1,0,
                    0,-1]

      H -> let s = 1/sqrt 2
          in  s * (2><2) [1, 1,
                          1,-1]