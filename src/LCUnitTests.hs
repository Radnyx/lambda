module LCUnitTests (unitTests) where

import Test.Tasty (testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import LC

ex_T = Lam (Lam (Var 1))
ex_F = Lam (Lam (Var 0))

ex_S = Lam (Lam (Lam (App (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))))
ex_K = ex_T

test_TF1 =
  testCase "TTF == T" $ assertEqual [] ex_T (reduce $ App (App ex_T ex_T) ex_F)

test_TF2 =
  testCase "FTF == F" $ assertEqual [] ex_F (reduce $ App (App ex_F ex_T) ex_F)

test_SKI =
  testCase "SKSK == KK(SK)" $ assertEqual []
    (reduce $ App (App (App ex_S ex_K) ex_S) ex_K) (reduce $ App (App ex_K ex_K) (App ex_S ex_K))

test_eta1 =
  testCase "\\\\(1 0) ==> \\0" $ assertEqual []
    (Lam (Var 0)) (reduce $ Lam (Lam (App (Var 1) (Var 0))))

test_eta2 =
  testCase "\\\\(0 0) ==> \\\\(0 0)" $ assertEqual [] (Lam (App (Var 0) (Var 0))) (reduce $ Lam (App (Var 0) (Var 0)))

unitTests =
  testGroup
    "Lambda Calculus -- Unit Tests"
    [test_TF1, test_TF2, test_SKI, test_eta1, test_eta2]
