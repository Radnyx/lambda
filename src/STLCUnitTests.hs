module STLCUnitTests (unitTests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Data.Maybe
import STLC

infixr 7 .->
(.->) = Fun

infixl 7 $$
($$) = App

λ = Lam

ex_IA = λ (Typ 0) (Var 0)
ex_KAB = λ (Typ 0) (λ (Typ 1) (Var 1))
ex_SABC = λ (Typ 0 .-> Typ 1 .-> Typ 2)
         (λ (Typ 0 .-> Typ 1)
         (λ (Typ 0)
            (Var 2 $$ Var 0 $$ (Var 1 $$ Var 0))))
ex_compABC =
  (λ (Typ 1 .-> Typ 2)
  (λ (Typ 0 .-> Typ 1)
  (λ (Typ 0) (Var 2 $$ (Var 1 $$ Var 0)))))

test_reduce1 =
  testCase "\\a : A. (\\b : A. b) a ==> \\a : A. a" $ assertEqual []
    ex_IA (reduce $ Lam (Typ 0) (App (Lam (Typ 0) (Var 0)) (Var 0)))

test_type1 =
  testCase "(\\a : A. a) : A -> A" $ assertEqual []
    (Just $ Typ 0 .-> Typ 0) (check ex_IA)

test_type2 =
  testCase "(\\a : A. \\b : B. a) : A -> B -> A" $ assertEqual []
    (Just $ Typ 0 .-> Typ 1 .-> Typ 0) (check ex_KAB)

test_type3 =
  testCase "(\\f : A. \\g : B. \\x : C. f x (g x)) : (A -> B -> C) -> (A -> B) -> A -> C" $ assertEqual []
    (Just $ Fun (Fun (Typ 0) (Fun (Typ 1) (Typ 2))) (Fun (Fun (Typ 0) (Typ 1)) (Fun (Typ 0) (Typ 2)))) (check ex_SABC)

test_type4 =
  testCase "(\\a : A -> A. a) (\\a : A . A) : A -> A)" $ assertEqual []
    (Just $ Fun (Typ 0) (Typ 0)) (check $ App (Lam (Fun (Typ 0) (Typ 0)) (Var 0)) ex_IA)

test_type5 =
  testCase "(\\a : A. (\\b : B. b) a) : Nothing" $ assertEqual []
    Nothing (check $ Lam (Typ 0) (App (Lam (Typ 1) (Var 0)) (Var 0)))

test_type6 =
  testCase "(\\a : A. (\\b : A -> A. b) a) : Nothing" $ assertEqual []
    Nothing (check $ Lam (Typ 0) (App (Lam (Fun (Typ 0) (Typ 0)) (Var 0)) (Var 0)))

{- treats check and prove as inverses, assuming we have the smallest such proof of a theorem -}
-- identity/const are easy: abstract lambdas, apply hypothesis in context
test_prove1 =
  testCase "prove identity" $ assertEqual []
    (ex_IA) (prove (fromJust $ check ex_IA))

test_prove2 =
  testCase "prove const" $ assertEqual []
    (ex_KAB) (prove (fromJust $ check ex_KAB))

-- proofs requiring application are MUCH more difficult
test_prove3 =
  testCase "prove composition" $ assertEqual []
    (ex_compABC) (prove (fromJust $ check ex_compABC))

test_prove4 =
  testCase "prove S-combinator" $ assertEqual []
    (ex_SABC) (prove (fromJust $ check ex_SABC))

unitTests =
  testGroup
    "Simply Typed Lambda Calculus -- Unit Tests"
    [test_reduce1, test_type1, test_type2, test_type3, test_type4, test_type5, test_type6,
     test_prove1, test_prove2, test_prove3, test_prove4]
