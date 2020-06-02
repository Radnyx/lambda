{-
  TODO:
  - test proof of distributivity of multiplication (annoying algebra ...)
  - test ackermann's function (compute modest values)
  - forall a b c, a < b -> b < c -> a < c where
  	lt x y := forall z, y + z = x -> False
  - proofs involving divisibility:
     let x | y := exists z : N, x * z = y
     let coprime x y := forall u : N, u | x -> u | y -> u = 1
    generalized euclid's lemma:
     forall a b c : N, a | bc -> coprime a b -> a | c
	

    (general)
-}

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
proof_eqSym = forceParse "\\n : N. \\m : N. \\H : n = m. eqElim (\\x:N.x = n) (refl n) H"

theorem_plus0 :: Term
theorem_plus0 = (reduce $ (App (forceParse
  "\\plus:N->N->N. forall x : N. plus x 0 = x") addition))

proof_plus0 :: Term
proof_plus0 = reduce $
  (App
    (forceParse $
      "\\plus:N->N->N. \\x:N. natElim (\\n:N. plus n 0 = n) (refl 0) " ++
        "(\\n:N.\\H:(plus n 0 = n). eqElim (\\x:N. S (plus n 0) = S x)" ++
          "(refl (S (plus n 0))) H) x")
    addition)

theorem_plusSucc :: Term
theorem_plusSucc = (reduce $ (App (forceParse
  "\\plus:N->N->N. forall x : N. forall y : N. plus x (S y) = S (plus x y)") addition))

proof_plusSucc :: Term
proof_plusSucc = reduce $
  (App
    (forceParse $
      "\\plus:N->N->N. \\x:N.\\y:N. natElim (\\n:N. plus n (S y) = S (plus n y)) " ++
        " (refl (S y)) (\\n:N.\\H:(plus n (S y) = S (plus n y)). eqElim " ++
          "(\\m:N. S (plus n (S y)) = S m) (refl (S (plus n (S y)))) H) x")
    addition)

theorem_lt0 :: Term
theorem_lt0 = (reduce $ (App (forceParse
  "\\plus:N->N->N. forall x : N. (forall z : N. plus 0 z = x -> F) -> F") addition))

proof_lt0 :: Term
proof_lt0 = (reduce $ (App (forceParse
  "\\plus:N->N->N. \\x : N. \\H : (forall z : N. plus 0 z = x -> F). H x (refl x)") addition))

test_parse1 =
  testCase "parse \"\\x : N. x\"" $ assertEqual []
    (Lam Nat (Var 0)) (forceParse "\\x : N. x")

test_parse2 =
  testCase "parse \"\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) (refl n) H\"" $ assertEqual []
    (Lam Nat (Lam Nat (Lam (Equal (Var 1) (Var 0))
      (EqElim (Lam Nat (Equal (Var 0) (Var 3))) (App Refl (Var 2)) (Var 0)))))
    (forceParse
      "\\n:N.\\m:N.\\H:(n = m). eqElim (\\x:N.x = n) (refl n) H")

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
    (reduce $ App (forceParse "\\plus : N -> N -> N. plus 2 4") addition)
    (reduce $ App (forceParse "\\plus : N -> N -> N. plus 4 2") addition)

test_reduce3 =
  testCase "5 + 3 == 8" $ assertEqual []
    (forceParse "8")
    (reduce $ App (forceParse "\\plus : N -> N -> N. plus 5 3") addition)

test_check1 =
  testCase "type-check addition" $ assertEqual []
    (forceParse "N -> N -> N")
    (fromSuccess $ check addition)

test_proof msg th prf = testCase msg $ assertEqual [] th (fromSuccess $ check prf)

test_proof1 = test_proof "proof of symmetry of equality" theorem_eqSym proof_eqSym

test_proof2 = test_proof "proof that x + 0 = x" theorem_plus0 proof_plus0

test_proof3 = test_proof "proof that x + S y = S (x + y)" theorem_plusSucc proof_plusSucc

test_proof4 = test_proof "proof that x < 0 -> F" theorem_lt0 proof_lt0

unitTests =
  testGroup
    "Logical Framework Lambda Calculus -- Unit Tests"
    [test_parse1, test_parse2, test_parse3,
     test_check1,
     test_reduce1, test_reduce2, test_reduce3,
     test_proof1, test_proof2, test_proof3, test_proof4]
