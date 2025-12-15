module Quantumize where

import AST
import Control.Monad.State
import HQP.QOp.Syntax

data Register
  = Input Int
  | Ancilla Int
  | Output
  deriving(Show, Eq)

-- Operands come before result
data Instr
  = InstrAND Register Register Register
  | InstrXOR Register Register Register
  | InstrNEG Register Register
  | InstrCopy Register Register
  deriving(Show, Eq)

data CompilerState = CompilerState {
  next :: Int,
  instrs :: [Instr]
}

type Compiler = State CompilerState

alloc :: Compiler Register
alloc = do
  CompilerState next instrs <- get
  put $ CompilerState (next + 1) instrs
  pure $ Ancilla next

emit :: [Instr] -> Compiler ()
emit toAdd = do
  cs <- get
  put $ cs {instrs = instrs cs ++ toAdd}

compile' :: Exp -> Compiler Register
compile' (Var n) = pure $ Input n
compile' (AND e1 e2) = do
  in1 <- compile' e1
  in2 <- compile' e2
  out <- alloc
  emit [InstrAND in1 in2 out]
  pure out
compile' (OR e1 e2) = compile' $ elimORwXOR $ OR e1 e2
compile' (XOR e1 e2) = do
  in1 <- compile' e1
  in2 <- compile' e2
  out <- alloc
  emit [InstrXOR in1 in2 out]
  pure out
compile' (NEG e) = do
  input <- compile' e
  out <- alloc
  emit [InstrNEG input out]
  pure out

initialState :: CompilerState
initialState = CompilerState { next = 0, instrs = [] }

compile :: Exp -> ([Instr], Int)
compile expr = (instrs result, next result)
  where
    (_, result) = runState compiler initialState
    compiler = do
      out <- compile' expr
      CompilerState _ instrs <- get
      emit [InstrCopy out Output]
      emit $ reverse instrs

type CircuitWidth = Int

pow :: QOp -> Int -> QOp
pow _ 0 = One
pow op p = op <.> pow op (p-1)

reorder :: (Int, Int) -> (Int, Int)
reorder (i, j) = if i > j then (j, i) else (i, j)

swap :: CircuitWidth -> (Int, Int) -> QOp
swap n (i0, j0) = Permute $ [0..i-1] ++ [j] ++ [i+1..j-1] ++ [i] ++ [j+1..n-1]
  where (i, j) = reorder (i0, j0)

ccx :: CircuitWidth -> Int -> Int -> Int -> QOp
ccx n i j k =
  swap n (i, 0) <> swap n (j, 1) <> swap n (k, 2) <> C (C X) <.> pow I (n - 3) <> swap n (i, 0) <> swap n (j, 1) <> swap n (k, 2) 

cx :: CircuitWidth -> Int -> Int -> QOp
cx n i j = 
  swap n (i, 0) <> swap n (j, 1) <> C X <.> pow I (n - 2) <> swap n (i, 0) <> swap n (j, 1)

registerToPos :: Int -> Register -> Int
registerToPos _ Output = 0
registerToPos _ (Input i) = i + 1
registerToPos n (Ancilla i) = n + i

quantumize :: (Int, Int) -> [Instr] -> QOp
quantumize (n, m) [] = pow I width
  where width = n + m + 1
quantumize (n, m) (instr : instrs) = quantumize (n, m) instrs <> operation
  where
    width = n + m + 1
    operation = case instr of
      InstrAND in1 in2 out -> 
        ccx width (registerToPos n in1) (registerToPos n in2) (registerToPos n out)
      InstrXOR in1 in2 out -> 
        cx width (registerToPos n in1) (registerToPos n out) <> cx width (registerToPos n in2) (registerToPos n out)
      InstrNEG input output -> 
        cx width (registerToPos n input) (registerToPos n output)
      InstrCopy from to -> 
        cx width (registerToPos n from) (registerToPos n to)