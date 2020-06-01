module LFUnitTests (unitTests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Data.Maybe

import LF
import LFParser

forceParse :: String -> Term
forceParse s =
  case doParse s of
    Right t -> t
    Left e -> error $ show e

addition :: Term
addition = forceParse "\\n:N.natElim (\\_:N.N->N) (\\x:N.x) (\\_:N.\\f:N->N.\\m:N.S (f m)) n"

test_parse1 =
  testCase "parse \"\\x : N. x\"" $ assertEqual []
    (Lam Nat (Var 0)) (forceParse "\\x : N. x")

test_parse2 =
  testCase "parse \"\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) n (refl n) m H\"" $ assertEqual []
    (Lam Nat (Lam Nat (Lam (Equal (Var 1) (Var 0))
      (EqElim (Lam Nat (Equal (Var 0) (Var 3))) (Var 2) (Refl (Var 2)) (Var 1) (Var 0)))))
    (forceParse
      "\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) n (refl n) m H")

test_parse3 =
  testCase "parse \"\\f:(forall _:N. N).\\x:N.\\y:N.f x y\"" $ assertEqual []
    (Lam (Pi Nat Nat) (Lam Nat (Lam Nat (App (App (Var 2) (Var 1)) (Var 0)))))
    (forceParse "\\f:(forall _:N. N).\\x:N.\\y:N.f x y")

test_reduce1 =
  testCase "\"(\\x : N. \\y : N. x = y) 0 (S 0)\" == \"0 = S 0\"" $ assertEqual []
    (forceParse "0 = S 0")
    (reduce $ forceParse "(\\x : N. \\y : N. x = y) 0 (S 0)")

test_check1 =
  testCase "type-check addition" $ assertEqual []
    (forceParse "N -> N -> N")
    (fromJust $ check addition)

unitTests =
  testGroup
    "Logical Framework Lambda Calculus -- Unit Tests"
    [test_parse1, test_parse2, test_parse3, test_reduce1, test_check1]
