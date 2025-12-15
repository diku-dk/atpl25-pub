module Grovers where

import AST
import Quantumize
import HQP.QOp.Syntax

prepareOracle :: Int -> QOp
prepareOracle 0 = One
prepareOracle n = prepareOracle (n-1) <.> I <> cx n 0 n

mcz :: Int -> QOp
mcz 1 = Z
mcz n = C $ mcz $ n-1

diffusion :: CircuitWidth -> QOp
diffusion width = pow H width <> pow X width <> mcz width <> pow X width <> pow H width

grovers :: Int -> CircuitWidth -> QOp -> QOp
grovers 0 width _ = pow H width
grovers n width oracle = grovers (n-1) width oracle <> diffusion width <> prepareOracle width <> oracle

count :: CircuitWidth -> QOp
count = undefined

inverseQFT :: QOp
inverseQFT = undefined