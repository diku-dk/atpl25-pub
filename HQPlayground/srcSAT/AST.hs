module AST where 

data Exp = 
    Atom String
  | AND Exp Exp 
  | OR Exp Exp
  | XOR Exp Exp 
  | NEG Exp