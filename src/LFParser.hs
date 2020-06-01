{-- Parse terms of Logical Framework/λΠ --}
{- TODO:
   - parse numbers as S (S (S ...))
   - better term parsers for infix operation precedence
     (necessary for \/ and /\ when implemented)
  - T, F, unit

  Precedence of infix operators (from weakest to strongest):
    ->
    \/
    /\
    =
-}

module LFParser (doParse) where

import Text.ParserCombinators.Parsec
import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import LF

type Bindings = M.Map String Int

{- Reserved identifiers, these cannot be bound. -}
reserved :: S.Set String
reserved = S.fromList ["forall", "S", "N", "natElim", "eqElim", "refl"]

skipwhite :: Parser ()
skipwhite = skipMany $ oneOf " \t"

ident :: Parser String
ident = do
  c <- letter
  cs <- many alphaNum
  return (c:cs)

{- Parses just a single simple term, or an application of several. -}
parseApp :: Bindings -> Parser Term
parseApp ctx = -- left associative
  foldl1 App <$> many1 (try $ parseSimple ctx)

{- Since the axioms behave like application, treat these as so. -}
parseAppOrAxiom :: Bindings -> Parser Term
parseAppOrAxiom ctx =
  choice (($ ctx) <$> [ parseRefl, parseNatElim, parseEqElim, parseApp ])

{- Pi or Lambda abstractions. -}
abstract :: String -> (Term -> Term -> Term) -> Bindings -> Parser Term
abstract str f ctx = do
  _ <- try $ string str
  skipwhite
  name <- ident <|> string "_"
  guard $ not (S.member name reserved)
  skipwhite
  _ <- char ':'
  t1 <- try (parseArrow ctx) <|> parseSimple ctx
  skipwhite
  _ <- char '.'
  let ctx' = M.insert name (M.size ctx) ctx
  f t1 <$> parseTerm ctx'

parseLam = abstract "\\" Lam
parsePi  = abstract "forall" Pi

parseVar :: Bindings -> Parser Term
parseVar ctx = do
  name <- ident
  guard $ not (S.member name reserved)
  guard (M.member name ctx)
  case M.lookup name ctx of
    Just i -> return $ Var (M.size ctx - i - 1)
    Nothing -> unexpected $ "Name \"" ++ name ++ "\" is not bound."

parseNat  _ = try $ string "N" >> return Nat
parseNum _ =
  return $ toNat (read <$> many1 digit) where
    toNat 0 = Zero
    toNat n = App Succ (toNat (n - 1))

parseSucc _ = try $ string "S" >> return Succ
parseUniv _ = try $ string "*" >> return Univ

{- NetElim actually forces the application of all of its arguments! -}
parseNatElim :: Bindings -> Parser Term
parseNatElim ctx =
   try $ string "natElim" >>
   NatElim <$> parseSimple ctx <*> parseSimple ctx
     <*> parseSimple ctx <*> parseTerm ctx

{- Equality has strongest precedence, behind applications. -}
parseEqualArg ctx =
  skipwhite >> (try (parseAppOrAxiom ctx) <|> parseSimple ctx)

parseEqual :: Bindings -> Parser Term
parseEqual ctx = do
  t1 <- parseEqualArg ctx
  skipwhite
  _ <- char '='
  Equal t1 <$> parseEqualArg ctx

parseRefl :: Bindings -> Parser Term
parseRefl ctx = do
  _ <- try $ string "refl"
  Refl <$> parseTerm ctx

parseEqElim :: Bindings -> Parser Term
parseEqElim ctx =
   try $ string "eqElim" >>
   EqElim <$> parseSimple ctx <*> parseSimple ctx
     <*> parseSimple ctx <*> parseSimple ctx <*> parseTerm ctx

parseParen :: Bindings -> Parser Term
parseParen ctx = do
  _ <- char '('
  t <- parseTerm ctx
  skipwhite
  _ <- char ')'
  return t

{- Arrow is weaker than application or equality. -}
parseArrowArgL ctx =
  skipwhite >> try (parseAppOrAxiom ctx <|> parseEqual ctx <|> parseSimple ctx)
{- Right associative: A -> B -> C == A -> (B -> C). -}
parseArrowArgR ctx =
  skipwhite >> (try (parseArrow ctx) <|> parseArrowArgL ctx)

parseArrow :: Bindings -> Parser Term
parseArrow ctx = do
  t1 <- parseArrowArgL ctx
  skipwhite
  _ <- try $ string "->"
  let ctx' = M.insert "_" (M.size ctx) ctx
  Pi t1 <$> parseArrowArgR ctx'

{- Parse most general terms and structures. -}
parseTerm :: Bindings -> Parser Term
parseTerm ctx = skipwhite >> choice ((\f -> try $ f ctx) <$>
  [parseLam, parsePi, parseArrow, parseEqual, parseAppOrAxiom ])

{- Most basic terms, recursion provided by parenthesis grouping. -}
parseSimple :: Bindings -> Parser Term
parseSimple ctx = skipwhite >> choice (($ ctx) <$>
  [ parseParen, parseSucc, parseNum, parseNat, parseUniv, parseVar ])

doParse :: String -> Either ParseError Term
doParse = parse (parseTerm M.empty) ""