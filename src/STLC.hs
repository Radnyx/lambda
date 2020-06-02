{-- Simply-Typed Lambda Calculus --}
{-
	Corresponds to intuitionistic propositional logic,
	where terms correspond to proofs in natural deduction.

	Corresponds to "cartesian closed categories", where
	(equiv. classes of) terms correspond to morphisms,
	and basic types are objects.
-}

{-# LANGUAGE TupleSections, LambdaCase, BlockArguments #-}

module STLC (Type(..), Term(..), reduce, check, prove) where

import Data.List
import Data.Char
import Data.Maybe
import Control.Monad
import qualified Data.Map.Strict as M

{- Generate a variable name given the index/depth. -}
name :: Int -> Char -> String
name i c = [ chr (i + ord c) ]

{- Map from relative indices to bound types. -}
type Context = M.Map Int Type

data Type =
    Fun Type Type -- τ -> τ
  | Typ !Int      -- choose any base type we care for
  deriving (Eq, Ord)

data Term =
    App Term Term -- e e
  | Lam Type Term -- λx:τ.e
  | Var !Int deriving (Eq, Ord)

instance Show Type where
  show (Fun f@(Fun _ _) c) = "(" ++ show f ++ ") -> " ++ show c
  show (Fun a b) = show a ++ " -> " ++ show b
  show (Typ i) = name i 'A'

instance Show Term where
  show = aux 0 where
    aux k (Var i) = name (k - i - 1) 'a'
    aux k (App l1@(Lam _ _) l2@(Lam _ _)) = "(" ++ aux k l1 ++ ") (" ++ aux k l2 ++ ")"
    aux k (App l@(Lam _ _) t2) = "(" ++ aux k l ++ ") " ++ aux k t2
    aux k (App t1 l@(Lam _ _)) = aux k t1 ++ " (" ++ aux k l ++ ")"
    aux k (App t1 a@(App _ _)) = aux k t1 ++ " (" ++ aux k a ++ ")"
    aux k (App t1 t2) = aux k t1 ++ " " ++ aux k t2
    aux k (Lam a t) = "\\" ++ name k 'a' ++ " : " ++ show a ++ ". " ++ aux (k + 1) t


{- Fold over term. Compares indices with lambda depth. -}
fold :: (a -> a -> a)     -- fold Applications
     -> (Type -> a -> a)  -- fold Lambdas
     -> (Int -> a)        -- fold Variables
     -> (Int -> Int -> a) -- depth  < var index
     -> (Int -> Int -> a) -- depth == var index
     -> Term -> a
fold app lm vr lt eq = aux 0 where
  aux i (App t1 t2) = app (aux i t1) (aux i t2)
  aux i (Lam a t') = lm a (aux (i + 1) t')
  aux i (Var j)
    | i  < j = lt i j -- free vars
    | i == j = eq i j -- latest binding
    | otherwise = vr j

{- Substitute latest binding with term t. -}
subst t = fold App Lam Var (\_ j -> Var (j - 1)) (\i _ -> addfree i t)
{- Add k to every free/latest variable index. -}
addfree k = fold App Lam Var f f where f _ j = Var (j + k)
{- True if contains latest binding. -}
free = fold (||) (const id) (const False) (\_ _ -> False) (\_ _ -> True)

{- Recursively compute βη on a term. -}
reduce :: Term -> Term
reduce (App t1 t2) =
  case (reduce t1, reduce t2) of
    -- β reduction
    (Lam _ t1', t2') -> reduce $ subst t2' t1'
    (      t1', t2') -> App t1' t2'
reduce (Lam _ (App t (Var 0)))
  -- η reduction
  | not (free t) = addfree (-1) t
reduce (Lam a t) = Lam a (reduce t)
reduce t = t

{- Type-check an explicitly typed term. -}
check :: Term -> Maybe Type
check = aux M.empty where
  aux :: Context -> Term -> Maybe Type
  aux γ (App f x) = do
    ft <- aux γ f
    xt <- aux γ x
    case ft of -- modus ponens
      Fun a b -> guard (a == xt) >> return b
      Typ _ -> Nothing
  aux γ (Lam a t) = -- direct proof
    Fun a <$> aux (M.insert (M.size γ) a γ) t
  aux γ (Var i) =
    M.lookup (M.size γ - i - 1) γ

{- Search for a proof of the given theorem.
   Not guaranteed to halt. -}
prove :: Type -> Term
prove theorem = (fromJust . msum) $
    (\n -> aux M.empty n theorem) <$> [1..] where

  -- return the arguments of a type
  args = \case { (Fun a b) -> a : args b ; _ -> [] }
  -- return the rightmost (returned) type
  ret = \case { (Fun _ b) -> ret b ; t -> t }
  -- given f [..., y, x], creates term (f (x (y ...)))
  apply t = \case { [] -> t ; x:xs -> App (apply t xs) x }

  aux :: Context -> Int -> Type -> Maybe Term
  aux γ 0 τ = -- Proof of size 0, immediately apply from context
    Var . (M.size γ - 1 -) . fst <$> find ((==τ) . snd) (M.toList γ)
  aux γ n (Fun a b) = -- Proof of function type, abstract lambda
    Lam a <$> aux (M.insert (M.size γ) a γ) (n - 1) b
  aux γ n τ = do
    -- first hypothesis with provable subgoals
    (i, goals) <- msum $ (\(i, g) -> (i,) <$> g) <$> M.toList
      -- prove each sub-goal
      -- BUG: doesn't exhaust EXACTLY n elements, this is because
      --      each branch copies (n - cost) independently ...
      (M.map (\(as, cost, _) -> mapM (aux γ (n - cost)) as) $
      -- return type matches, won't exceed size limit
       M.filter (\(_, cost, σ) -> σ == τ && cost <= n) $
      -- for each hypothesis, compute arguments/return type
       M.map (\σ -> let as = args σ in (as, length as, ret σ)) γ)
    return $ apply (Var (M.size γ - 1 - i)) (reverse goals)