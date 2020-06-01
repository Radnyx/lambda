module LFUnitTests (unitTests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import LF
import LFParser

forceParse :: String -> Term
forceParse s =
  case doParse s of
    Right t -> t
    Left e -> error $ show e

addition :: Term
addition = forceParse "\\n:N.natElim (\\_:N.N->N) (\\x:N.x) (\\_:N.\\f:N->N.\\m:N.S (f m)) n"

theorem_eqSym :: Term
theorem_eqSym = forceParse "forall n : N. forall m : N. forall _ : n = m. m = n"

proof_eqSym :: Term
proof_eqSym = forceParse "\\n : N. \\m : N. \\H : n = m. eqElim (\\x:N.x = n) n (refl n) m H"

theorem_plus0 :: Term
theorem_plus0 = (reduce $ (App (forceParse
  "\\plus:N->N->N. forall x : N. plus x 0 = x") addition))

--proof_plus0 :: Term

test_parse1 =
  testCase "parse \"\\x : N. x\"" $ assertEqual []
    (Lam Nat (Var 0)) (forceParse "\\x : N. x")

test_parse2 =
  testCase "parse \"\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) n (refl n) m H\"" $ assertEqual []
    (Lam Nat (Lam Nat (Lam (Equal (Var 1) (Var 0))
      (EqElim (Lam Nat (Equal (Var 0) (Var 3))) (Var 2) (App Refl (Var 2)) (Var 1) (Var 0)))))
    (forceParse
      "\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) n (refl n) m H")

test_parse3 =
  testCase "parse \"\\f:(forall _:N. N).\\x:N.\\y:N.f x y\"" $ assertEqual []
    (Lam (Pi Nat Nat) (Lam Nat (Lam Nat (App (App (Var 2) (Var 1)) (Var 0)))))
    (forceParse "\\f:(forall _:N. N).\\x:N.\\y:N.f x y")

test_reduce1 =
  testCase "\"(\\x : N. \\y : N. x = y) 0 1\" == \"0 = 1\"" $ assertEqual []
    (forceParse "0 = 1")
    (reduce $ forceParse "(\\x : N. \\y : N. x = y) 0 1")

test_reduce2 =
  testCase "2 + 4 == 4 + 2" $ assertEqual []
    (reduce $ (App (forceParse "\\plus : N -> N -> N. plus 2 4") addition))
    (reduce $ (App (forceParse "\\plus : N -> N -> N. plus 4 2") addition))

test_reduce3 =
  testCase "5 + 3 == 8" $ assertEqual []
    (forceParse "8")
    (reduce $ (App (forceParse "\\plus : N -> N -> N. plus 5 3") addition))

test_check1 =
  testCase "type-check addition" $ assertEqual []
    (forceParse "N -> N -> N")
    (fromSuccess $ check addition)

test_proof1 =
  testCase "proof of symmetry of equality" $ assertEqual []
    theorem_eqSym (fromSuccess $ check proof_eqSym)

unitTests =
  testGroup
    "Logical Framework Lambda Calculus -- Unit Tests"
    [test_parse1, test_parse2, test_parse3,
     test_check1,
     test_reduce1, test_reduce2, test_reduce3,
     test_proof1]
