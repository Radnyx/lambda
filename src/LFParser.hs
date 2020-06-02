{-- Parse terms of Logical Framework/λΠ --}
{- TODO:
   - parse numbers as S (S (S ...))
   - better term parsers for infix operation precedence
     (necessary for \/ and /\ when implemented)
   - T, F, unit
   - multiple bindings for a type, e.g.: forall x y : N. ...

  Precedence of infix operators (from weakest to strongest):
    ->
    \/
    /\
    =
-}

module LFParser (doParse) where

import Text.ParserCombinators.Parsec
import Data.Maybe
import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import LF

-- head of list is latest binding, shadows rest
type Bindings = (M.Map String [Int], Int)

bind :: String -> Bindings -> Bindings
bind name (ctx, depth) =
  if M.member name ctx
  then (M.insert name (depth : fromJust (M.lookup name ctx)) ctx, depth + 1)
  else (M.insert name [depth] ctx, depth + 1)

get :: String -> Bindings -> Maybe Int
get name (ctx, _) = do
  xs <- M.lookup name ctx
  guard $ not (null xs)
  return $ head xs

{- Reserved identifiers, these cannot be bound. -}
reserved :: S.Set String
reserved = S.fromList ["forall", "S", "N", "natElim", "eqElim", "refl", "F"]

skipwhite :: Parser ()
skipwhite = skipMany $ oneOf " \t"

ident :: Parser String
ident = do
  c <- letter
  cs <- many alphaNum
  return (c:cs)

appMany :: Bindings -> Parser [Term]
appMany ctx = do
  -- first application can be an axiomatic application
  x <- try (parseNatElim ctx) <|> try (parseEqElim ctx) <|> try (parseSimple ctx)
  xs <- many (try (parseSimple ctx))
  return (x : xs)

{- Parses just a single simple term, or an application of several. -}
parseApp :: Bindings -> Parser Term
parseApp ctx = -- left associative
  foldl1 App <$> appMany ctx

{- Pi or Lambda abstractions. -}
abstract :: String -> (Term -> Term -> Term) -> Bindings -> Parser Term
abstract str f b = do
  _ <- try $ string str
  skipwhite
  name <- ident <|> string "_"
  guard $ not (S.member name reserved)
  skipwhite
  _ <- char ':'
  t1 <- try (parseArrow b) <|> try (parseEqual b) <|> parseSimple b
  skipwhite
  _ <- char '.'
  f t1 <$> parseTerm (bind name b)

parseLam = abstract "\\" Lam
parsePi  = abstract "forall" Pi

parseVar :: Bindings -> Parser Term
parseVar b@(_, depth) = do
  name <- ident
  guard $ not (S.member name reserved)
  case get name b of
    Just i -> return $ Var (depth - i - 1)
    Nothing -> unexpected $ "Name \"" ++ name ++ "\" is not bound."

parseNum :: Bindings -> Parser Term
parseNum _ = do
  num <- many1 digit
  return $ toNat (read num :: Integer) where
    toNat 0 = Zero
    toNat n = App Succ (toNat (n - 1))
parseNat  _ = try $ string "N" >> return Nat
parseSucc _ = try $ string "S" >> return Succ
parseRefl _ = try $ string "refl" >> return Refl
parseBottom _ = try $ string "F" >> return Bottom

{- NetElim actually forces the application of all of its arguments! -}
parseNatElim :: Bindings -> Parser Term
parseNatElim ctx =
   try $ string "natElim" >>
   NatElim <$> parseSimple ctx <*> parseSimple ctx
     <*> parseSimple ctx <*> parseSimple ctx

{- Equality has strongest precedence, behind applications. -}
parseEqualArg ctx =
  skipwhite >> (try (parseApp ctx) <|> parseSimple ctx)

parseEqual :: Bindings -> Parser Term
parseEqual ctx = do
  t1 <- parseEqualArg ctx
  skipwhite
  _ <- char '='
  Equal t1 <$> parseEqualArg ctx

parseEqElim :: Bindings -> Parser Term
parseEqElim ctx =
   try $ string "eqElim" >>
   EqElim <$> parseSimple ctx <*> parseSimple ctx <*> parseSimple ctx

parseParen :: Bindings -> Parser Term
parseParen ctx = do
  _ <- char '('
  t <- parseTerm ctx
  skipwhite
  _ <- char ')'
  return t

{- Arrow is weaker than application or equality. -}
parseArrowArgL ctx =
  skipwhite >> (try (parseEqual ctx) <|> try (parseApp ctx) <|> parseSimple ctx)
{- Right associative: A -> B -> C == A -> (B -> C). -}
parseArrowArgR ctx =
  skipwhite >> (try (parseArrow ctx) <|> parseArrowArgL ctx)

parseArrow :: Bindings -> Parser Term
parseArrow ctx = do
  t1 <- parseArrowArgL ctx
  skipwhite
  _ <- try $ string "->"
  Pi t1 <$> parseArrowArgR (bind "_" ctx)

{- Parse most general terms and structures. -}
parseTerm :: Bindings -> Parser Term
parseTerm ctx = skipwhite >> choice ((\f -> try $ f ctx) <$>
  [parseLam, parsePi, parseArrow, parseEqual, parseApp ])

{- Most basic terms, recursion provided by parenthesis grouping. -}
parseSimple :: Bindings -> Parser Term
parseSimple ctx = skipwhite >> choice (($ ctx) <$>
  [ parseParen, parseSucc, parseNum, parseNat, parseRefl, parseBottom, parseVar ])

doParse :: String -> Either ParseError Term
doParse = parse (parseTerm (M.empty, 0)) ""