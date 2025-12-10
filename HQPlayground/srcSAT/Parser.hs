module Parser ( parse, ) where

import AST
import Data.Char (isAlphaNum)
import Control.Monad (ap,liftM,void)

type Error = String

newtype Parser a = Parser {runParser :: (String -> Either Error (String, a))}

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

eof :: Parser ()
eof = Parser $ \s -> case s of
  "" -> Right ("",())
  _  -> Left "Expected end of input"

space :: Parser ()
space = Parser $ \s -> Right (clean s,())
  where
    clean (s:s')
      | s == ' '  = clean s'
      | s == '\n' = clean s'
    clean s = s

lexeme :: Parser a -> Parser a
lexeme p = p <* space

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser $ \s ->
  case s of
    c : cs ->
      if p c
        then Right (cs, c)
        else Left $ c : " did not satisfy a predicate."
    _ -> Left "Empty input."

choice :: [Parser a] -> Parser a
choice [] = Parser $ \s -> Left $ "Illegal program: " ++ s
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

-- Include this only to ensure consistent whitespace handling using lexeme (easy to forget otherwise)
lVar:: Parser String
lVar = lexeme $ some $ satisfy isAlphaNum


parseAtom :: Parser Exp
parseAtom = choice
  [
    do
      x <- lVar
      pure $ Atom x,
    lString "(" *> parseExp <* lString ")"
  ]

parseExp :: Parser Exp
parseExp = choice
  [
    do
      lString "~"
      x <- parseExp1
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
  case runParser (parseExp <* eof) s of
    Right (_,res) -> Right res
    Left err      -> Left err
