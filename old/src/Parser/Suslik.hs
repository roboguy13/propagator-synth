module Parser.Suslik
  where

import           Control.Applicative (liftA2)

-- import           Parser
import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Parser.Suslik.ADT

type Parser a = Parsec String String a

parseName :: Parser String
parseName = some (alphaNumChar <|> char '_')

parsePredicate :: Parser SPredicate
parsePredicate = do
  chunk "predicate"
  some space
  SPredicate <$> parseName <*> parseArgDecls <*> parsePredicateBody

parseParen'd :: Parser a -> Parser [a]
parseParen'd p = char '(' *> many space *> fmap collapseMaybe (optional (go <* many space)) <* char ')'
  where
    go = liftA2 (:) p (char ',' *> many space *> go) <|> fmap (:[]) p

parseArgDecls :: Parser [VarDecl]
parseArgDecls = parseParen'd parseVarDecl

collapseMaybe :: Maybe [a] -> [a]
collapseMaybe Nothing = []
collapseMaybe (Just xs) = xs

parsePredicateBody :: Parser [PredicateBranch]
parsePredicateBody = char '{' *> many space *> go <* many space <* char '}'
  where
    go = some parsePredicateBranch

parsePredicateBranch :: Parser PredicateBranch
parsePredicateBranch = PredicateBranch <$> parsePureProp <*> parseSProp

parsePureProp :: Parser PureProp
parsePureProp =
  (chunk "true" *> pure (BoolLit True)) <|>
  (chunk "false" *> pure (BoolLit False)) <|>
  parseBinOp parsePureProp ["&&", "/\\"] And <|>
  parseBinOp parsePureProp ["||", "\\/"] Or <|>
  parseBinOp parseExpr ["==", "=i"] Equal <|>
  parseBinOp parseExpr ["<="] Le <|>
  (chunk "not" *> some space *> fmap Not parsePureProp) <|>
  (char '(' *> many space *> parsePureProp <* many space <* parsePureProp)

parseBinOp :: Parser a -> [String] -> (a -> a -> b) -> Parser b
parseBinOp parser names op = do
  x <- parser
  many space
  foldr1 (<|>) (map chunk names)
  many space
  y <- parser
  pure (op x y)

parseBinOp' :: Parser a -> String -> (a -> a -> b) -> Parser b
parseBinOp' parser name = parseBinOp parser [name]

parseExpr :: Parser Expr
parseExpr =
  (fmap (Lit . read) (some digitChar)) <|>
  (fmap ExprVar parseName) <|>
  (parseBinOp' parseExpr "+" Add) <|>
  (parseBinOp' parseExpr "*" Add) <|>
  (parseBinOp' parseExpr "++" SetUnion) <|>
  parseSetLit <|>
  (char '{' *> many space *> char '}' *> pure SetEmpty)

parseSetLit :: Parser Expr
parseSetLit = fmap SetLit (char '{' *> go <* char '}')
  where
    go = liftA2 (:) parseExpr (char ',' *> many space *> go) <|> fmap (:[]) parseExpr

parseSProp :: Parser SProp
parseSProp = undefined

parseVarDecl :: Parser VarDecl
parseVarDecl = VarDecl <$> parseType <*> parseName

parseType :: Parser SuslikType
parseType =
  (chunk "int" *> pure IntType) <|>
  (chunk "set" *> pure SetType) <|>
  (chunk "loc" *> pure LocType)

