module Parser ( parse, ) where

import AST
import Data.Char (isAlphaNum)
import Control.Monad (ap,liftM,void)

type Error = String
type VTable = [(String,Int)]
type ParserState = (String,VTable)

newtype Parser a = Parser {runParser :: (ParserState -> Either Error (ParserState, a))}

instance Functor Parser where
  fmap = liftM

instance Applicative Parser where
  pure x = Parser $ \tok -> Right (tok, x)
  (<*>) = ap

instance Monad Parser where
  Parser x >>= f = Parser $ \tok ->
    case x tok of
      Left err -> Left err
      Right (tok',x') ->
        let Parser y = f x'
         in y tok'

initTable :: VTable
initTable = []

eof :: Parser ()
eof = Parser $ \(s,v) -> case s of
  "" -> Right (("",v),())
  _  -> Left "Expected end of input"

space :: Parser ()
space = Parser $ \(s,v) -> Right ((clean s,v),())
  where
    clean (s:s')
      | s == ' '  = clean s'
      | s == '\n' = clean s'
    clean s = s

lexeme :: Parser a -> Parser a
lexeme p = p <* space

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser $ \(s,v) ->
  case s of
    c : cs ->
      if p c
        then Right ((cs,v), c)
        else Left $ c : " did not satisfy a predicate."
    _ -> Left "Empty input."

choice :: [Parser a] -> Parser a
choice [] = Parser $ \(s,_) -> Left $ "Illegal program: " ++ s
choice (p:ps) = Parser $ \s ->
  case runParser p s of
    Left _ -> runParser (choice ps) s
    Right (s',x) -> Right (s',x)

many :: Parser a -> Parser [a]
many p =
  choice
    [ do
        x <- p
        xs <- many p
        pure $ x : xs,
      pure []
    ]

some :: Parser a -> Parser [a]
some p = do
  x <- p
  xs <- many p
  pure (x:xs)

chunk :: String -> Parser String
chunk [] = pure ""
chunk (c : cs) = do
  void $ satisfy (== c)
  void $ chunk cs
  pure $ c : cs

lString :: String -> Parser ()
lString s = lexeme $ void $ chunk s

-- Include this only to ensure consistent whitespace handling using lexeme (easy to forget otherwise).
lVar:: Parser String
lVar = lexeme $ some $ satisfy isAlphaNum

getEnv :: Parser VTable
getEnv = Parser $ \(s,v) -> Right ((s,v),v)

modEnv :: (VTable -> VTable) -> Parser ()
modEnv f = Parser $ \(s,v) -> Right ((s,f v),())

-- A transformer literal. Consumes a variable, and looks up/stores that variable in the environment,
-- and maps each unique variable to one unique integer.
tVar :: Parser Int
tVar = do
  v <- lVar
  env <- getEnv
  case lookup v env of
    Just x -> pure x
    Nothing ->
      let s = length env
       in do 
            modEnv (\table -> (v,s) : table)
            pure s


parseAtom :: Parser Exp
parseAtom = choice
  [
    do
      x <- tVar
      pure $ Var x,
    lString "(" *> parseExp <* lString ")"
  ]

parseExp :: Parser Exp
parseExp = choice
  [
    do
      lString "~"
      x <- parseAtom
      pure $ NEG x,
    do
      x <- parseAtom
      lString "&"
      y <- parseExp
      pure $ AND x y,
    do
      x <- parseAtom
      lString "|"
      y <- parseExp
      pure $ OR x y,
    do
      x <- parseAtom
      lString "^"
      y <- parseExp
      pure $ XOR x y,
    parseAtom
  ]


parse :: String -> Either Error Exp
parse s = 
  case runParser (parseExp <* eof) (s,initTable) of
    Right (_,res) -> Right res
    Left err      -> Left err
