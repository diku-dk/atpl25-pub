module Main where

import Parser
import Quantumize
import Grovers

main :: IO ()
main = 
  let 
      -- obtain input - substitute appropriate input stream later
      example = "p & q | (123 & ~123) & ( (x ^ y) ^ z)"

      -- parse input
      bexp = 
        case parse example of
          Right x  -> x
          Left err -> error err

      -- quantumize boolean expression
      (instrs,s) = compile bexp
      qop = quantumize (s,s) instrs

      -- apply Grover's algorithm
      _ = undefined

      -- ???
      _ = undefined

      -- profit
   in undefined

