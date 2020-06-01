{-- (Untyped) Lambda Calculus --}
{-
	Turing complete, lacks normal forms.
-}

module LC (Term (..), subst, addfree, free, reduce) where

data Term =
    App Term Term
  | Lam Term
  | Var !Int deriving (Eq, Ord, Show)

{- Fold over term. Compares indices with lambda depth. -}
fold :: (a -> a -> a)     -- fold Applications
     -> (a -> a)          -- fold Lambdas
     -> (Int -> a)        -- fold Variables
     -> (Int -> Int -> a) -- depth  < var index
     -> (Int -> Int -> a) -- depth == var index
     -> Term -> a
fold ap lm vr lt eq = aux 0 where
  aux i (App t1 t2) = ap (aux i t1) (aux i t2)
  aux i (Lam t') = lm (aux (i + 1) t')
  aux i v@(Var j)
    | i  < j = lt i j -- free vars
    | i == j = eq i j -- latest binding
    | otherwise = vr j

{- Substitute latest binding with term t. -}
subst t = fold App Lam Var (\_ j -> Var (j - 1)) (\i _ -> addfree i t)

{- Add k to every free/latest variable index. -}
addfree k = fold App Lam Var f f where f _ j = Var (j + k)

{- True if term contains latest binding. -}
free = fold (||) id (const False) (\_ _ -> False) (\_ _ -> True)

{- Recursively compute βη on a term. -}
reduce :: Term -> Term
reduce (App t1 t2) =
  case (reduce t1, reduce t2) of
    -- β reduction
    (Lam t1', t2) -> reduce $ subst t2 t1'
    (    t1,  t2) -> App t1 t2
reduce (Lam (App t1 (Var 0)))
  -- η reduction
  | not (free t1) = addfree (-1) t1
reduce (Lam t) = Lam (reduce t)
reduce t = t
