module Main where

import Parser
import Quantumize
import Grovers
import Generator
import Eval
import Macros 
import Gates

main :: IO ()
main = 
  let 
      -- obtain input - substitute appropriate input stream later
      example = "p & q | (123 & ~123) & ( (x ^ y) ^ z)"
      n = 6

      -- parse input
      bexp = 
        case parse example of
          Right x  -> x
          Left err -> error err

      -- quantumize boolean expression
      (instrs,m) = compile bexp
      qop = quantumize (n,m) instrs

      -- apply Grover's algorithm
      width = n + m + 1
      iterations = 1
      groversCircuit = grovers width qop iterations

      -- ???
      h = evalProgram (pow H width) (zero width)
      result = evalByParts 1 qop h
      -- profit
   in result >>= pp