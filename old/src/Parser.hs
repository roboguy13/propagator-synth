{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wall -Wno-unused-do-bind #-}

module Parser
  where
  -- (Parser
  -- ,Parseable
  -- ,getParser
  -- ,parse
  -- ,noParse
  -- ,parseCharWhen
  -- ,parseChar
  -- ,parseOneOf
  -- ,parseNotOneOf
  -- ,parseString
  -- ,parseSpace
  -- ,parseNewline
  -- ,parseWhitespace
  -- ,parseBracketed
  -- ,parseSequence

  -- ,module Control.Applicative
  -- ) where

import           Control.Applicative
import           Control.Monad

import           Data.Bifunctor
import           Data.Char

import           Error.Error
import           Error.Render

newtype ParseError = MkParseError { getParseError :: Annotated }

pprParseError :: ParseError -> String
pprParseError (MkParseError ann) = renderAnnotated ann

data ErrorCtx = ErrorCtx
  { errLineNum :: Int
  , errColNum  :: Int
  , errLength :: Int
  , errRemainingSourceLines :: [String] -- | Starts with all the lines of the entire input
  }

-- TODO: Does this make sense?
instance Semigroup ErrorCtx where
  x <> _ = x

newtype Parser a = Parser { runParser :: (ErrorCtx, String) -> (ErrorCtx, Either ParseError (String, a)) }

ctxToSpan :: ErrorCtx -> Int -> Span
ctxToSpan ctx count = Span (errColNum ctx) count

currLine :: ErrorCtx -> String
currLine ctx =
  case errRemainingSourceLines ctx of
    [] -> error "currLine: Internal error: No lines remaining"
    (theLine:_) -> theLine

mkParseError :: ErrorCtx -> String -> ParseError
mkParseError ctx str = MkParseError (annotate (currLine ctx) [(ctxToSpan ctx (errLength ctx), Message Red str)])

mkParseError' :: ErrorCtx -> String -> (ErrorCtx, Either ParseError (String, a))
mkParseError' ctx errStr = (ctx, Left $ mkParseError ctx errStr)


parseError :: String -> Parser a
parseError str = do
  Parser $ \ (ctx, _) -> (ctx, Left (mkParseError ctx str))

newErrorCtx :: ErrorCtx -> ErrorCtx
newErrorCtx ctx = ctx { errLength = 0 }

-- initialErrorCtx :: ErrorCtx
-- initialErrorCtx = ErrorCtx 1 1

-- -- instance Ppr ErrorCtx where
-- --   ppr ctx =
-- --     unlines
-- --       [ "On line " ++ show (errLineNum ctx)
-- --       , "at column " ++ show (errColNum ctx)
-- --       ]

incrCol :: ErrorCtx -> ErrorCtx
incrCol ctx = ctx { errColNum = errColNum ctx + 1 }

incrLine :: ErrorCtx -> ErrorCtx
incrLine ctx = ctx { errLineNum = errLineNum ctx + 1, errColNum = 1 }

updateCtxForChar :: ErrorCtx -> Char -> ErrorCtx
updateCtxForChar ctx c =
  if c `elem` "\n\r"
    then incrLine ctx { errRemainingSourceLines = drop 1 $ errRemainingSourceLines ctx }
    else incrCol ctx

execParser :: Parser a -> String -> Either ParseError a
execParser p s =
  let theLines = lines s
      initialErrorCtx = ErrorCtx 1 1 0 theLines
  in
  case runParser p (initialErrorCtx, s) of
    (_, Right (_, x)) -> Right x
    (_, Left err) -> Left err

instance Functor Parser where
  fmap f (Parser p) = Parser $ (fmap . fmap) (second f) . p

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return x = Parser (\(ctx, s) -> (ctx, return (s, x)))

  Parser p >>= f = Parser $ \(ctx, s) -> do
    case p (ctx, s) of
      (ctx', Right (s', x)) ->
        runParser (f x) (ctx', s')
      (ctx', Left err) -> (ctx', Left err)

instance Semigroup (Parser a) where
  Parser p <> Parser q = Parser $ \arg -> p arg <> q arg

instance Alternative Parser where
  empty = Parser $ \(ctx, _) -> (ctx, Left $ error "Alternative Parser: empty")
  (<|>) = (<>)


parseCharWhen :: String -> (Char -> Bool) -> Parser Char
parseCharWhen errStr f = Parser $ \case
  (ctx, (c:cs))
    | f c -> (updateCtxForChar ctx c, return (cs, c))
  (ctx, (c:_)) -> (ctx, Left $ mkParseError ctx ("parseCharWhen: Saw " <> show c <> ", expected " <> errStr))
  (ctx, []) -> (ctx, Left $ mkParseError ctx $ "parseCharWhen: Empty. Expected " <> errStr)

token :: Parser a -> Parser a
token (Parser p) = Parser $ \(ctx, str) ->
  p (newErrorCtx ctx, str)

parseChar :: Char -> Parser Char
parseChar c = parseCharWhen (show c) (== c)

parseAlphaUnderscore :: Parser Char
parseAlphaUnderscore = parseChar '_' <> parseCharWhen "isAlpha" isAlpha

parseDigit :: Parser Char
parseDigit = parseCharWhen "isDigit" isDigit

parseNum :: Parser Integer
parseNum = token $ read <$> some parseDigit

parseKeyword :: String -> Parser String
parseKeyword = token . \case
  [] -> return ""
  (c:cs) -> (:) <$> parseChar c <*> parseKeyword cs

parseEndOfInput :: Parser ()
parseEndOfInput = Parser $ \(ctx, str) -> case str of
  "" -> (ctx, Right ("", ()))
  _ -> mkParseError' ctx "Expected end of input"

parseEOF :: Parser ()
parseEOF = do
  many (parseNewline <|> parseSpace)
  parseEndOfInput

-- -- parseFails :: Parser a -> Parser ()
-- -- parseFails p = Parser $ \s ->
-- --   case runParser p s of
-- --     Left _ -> Right (s, ())
-- --     Right _ -> Left "parseFails"

-- -- -- | Parse name characters occuring after the first character of a name

-- parseNameChar :: Parser Char
-- parseNameChar = token (parseAlphaUnderscore <|>  parseCharWhen "special character" (`elem` "{}()+-*/%^") <|> parseDigit)

-- parseName :: Parser String
-- parseName = (:) <$> parseNameChar <*> go
--   where
--     go = many parseNameChar

parseSpace :: Parser Char
parseSpace = parseChar ' ' <|> parseChar '\t' <|> parseNewline

parseNewline :: Parser Char
parseNewline = (parseChar '\n')

parseBinOp :: String -> Parser a -> Parser a -> Parser (a, a)
parseBinOp op p q = token $ do
  x <- p
  many parseSpace
  parseKeyword op
  many parseSpace
  y <- q
  return (x, y)

-- opt :: a -> Parser a -> Parser a
-- opt def p = p <|> return def

-- maybeParse :: Parser a -> Parser (Maybe a)
-- maybeParse p = fmap Just p <|> return Nothing

-- notOneOf :: [Char] -> Parser Char
-- notOneOf cs = parseCharWhen "notOneOf" (`notElem` cs)

-- class Parseable a where
--   parse :: Parser a

