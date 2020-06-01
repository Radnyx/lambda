{-- Logical Framework/λΠ --}
{-
	Corresponds to intuitionistic first-order predicate logic.

	EXTENDED with the following axioms:
		N       : *
		0       : ℕ
		S       : Π (_ : ℕ) . ℕ
		natElim : Π (P : Π (_ : ℕ) . *) . Π (_ : P 0) . Π (_ : Π (m : ℕ) . Π (_ : P m) . P (S m)) . Π (n : ℕ) . P n
		eqElim  : Π (P : Π (_ : ℕ) . *) . Π (x : ℕ) . Π (_ : P x) . Π (y : ℕ) . Π (_ : x = y) . P y
		(=)     : Π (_ : ℕ) . Π (_ : ℕ) . *
		refl    : Π (n : ℕ) . n = n

	With reduction rules for natElim on Zero/App Succ n.

	 This is a decently powerful system: first order predicates are definable and help perform
	rewrites or nat folds (iterated composition). This allows us to compute/prove totality of
	Ackermann's function. We lack polymorphism (second order quantification), so I believe we
	remain under the strength of Heyting Arithmetic.

	TODO:
	  - reduce probably needs an updated context for checking motives ???
	  - know when to reduce types
	  - reduction rule for natElim
	  - add categorical judgements (axioms):
	    |- T : *
		|- () : T
		|- F : *
		|- F -> P


	is uncountability of (nat -> nat) provable?
	 how difficult is it to do so automatically?



	Nice definitions:

      // x <= y when there is no z we can add to y to get x
	  Definition leq (x y : nat) :=
        forall z, y + z = x -> False.

    Theorems to try:

      // if two functions differ at a point, they are not equal
      forall (f : nat -> nat) (g : nat -> nat),
        ((forall x : nat, f x = g x) -> False) -> (f = g -> False)

      // with add_comm in context!!!
      forall x y : nat, x <= y -> x <= (S y)


	alternative formulation:
	  EVERYTHING is a Term,
	    "*" (kind) is untypable ??
-}

{-# LANGUAGE LambdaCase, BlockArguments, DeriveFunctor #-}

module LF (Term(..), check, reduce, fromSuccess) where

import qualified Data.Vector as V
import Data.Char
import Data.List
import Control.Monad
import Control.Applicative



type Context = V.Vector Term

data Term =
   App Term Term
 | Lam Term Term
 | Pi  Term Term
 | Var !Int -- de-bruijn index
 | Nat
 | Zero
 | Succ
 | NatElim Term Term Term Term
 | Equal Term Term
 | Refl
 | EqElim Term Term Term Term Term
 | Univ
 deriving (Eq, Ord)

{- TODO:
   - show "->" when free in type.
   - Sequences of App should omit parenthesis
   - remember parsed varible names as Maybe String in Var,
     obviously ignored during substitution
-}
instance Show Term where
  show = aux 0 where
    -- Generate a variable name given the index/depth.
    name :: Int -> Char -> String
    name i c = [ chr (i + ord c) ]

    -- surround non-simple terms with parenthesis
    paren :: Int -> Term -> String
    paren k a@(App _ _) = "(" ++ aux k a ++ ")"
    paren k a@(Lam _ _) = "(" ++ aux k a ++ ")"
    paren k a@(Pi _ _)  = "(" ++ aux k a ++ ")"
    paren k t = aux k t

    aux k (Var i) = name (k - i - 1) 'a'
    aux k (App t1 t2) = paren k t1 ++ " " ++ paren k t2
    aux k (Lam a t) = "\\" ++ name k 'a' ++ " : " ++ paren k a ++ ". " ++ aux (k + 1) t
    aux k (Pi a t) = "forall " ++ name k 'a' ++ " : " ++ paren k a ++ ". " ++ aux (k + 1) t
    aux k (NatElim p p0 pS n) =
      unwords ["natElim", paren k p, paren k p0, paren k pS, paren k n]
    aux k (EqElim p x px y xy) =
      unwords ["eqElim", paren k p, paren k x, paren k px, paren k y, paren k xy]
    aux k (Equal a b) = aux k a ++ " = " ++ aux k b
    aux _ Nat = "N"
    aux _ Zero = "0"
    aux _ Succ = "S"
    aux _ Refl = "refl"
    aux _ Univ = "*"

data Check a = Success a | Failure String deriving (Show, Functor)

instance Applicative Check where
  Success f <*> a = f <$> a
  Failure s <*> _ = Failure s
  pure = Success
instance Monad Check where
  Success a >>= f = f a
  Failure s >>= _ = Failure s

guardMsg :: Bool -> String -> Check ()
guardMsg True _ = Success ()
guardMsg False msg = Failure msg

fromSuccess :: Check a -> a
fromSuccess (Success a) = a
fromSuccess (Failure s) = error s


{- Term is ℕ. -}
tryNat :: Term -> String -> Check ()
tryNat Nat _ = return ()
tryNat _ msg = Failure msg

{- Term is Πx:A.B. -}
tryPi :: Term -> String -> Check (Term, Term)
tryPi (Pi t1 t2) _ = return (t1, t2)
tryPi _ msg = Failure msg

{- Term is Πx:ℕ.*.
   `msg` is name of eliminator ("NatElim" or "EqElim"). -}
tryMotive :: Term -> String -> Check ()
tryMotive t msg = do
  (t1, t2) <- tryPi t $ msg ++ " motive " ++ show t ++ " be a function, got " ++ show t ++ "."
  tryNat t1 $ msg ++ " motive " ++ show t ++ " argument must be Nat, got " ++ show t1 ++ "."
  case t2 of
    Univ -> return ()
    _ -> Failure $ msg ++ " motive " ++ show t ++ " must return a type, got " ++ show t1 ++ "."

{- Term is x = y. -}
tryEqual :: Term -> Term -> Term -> String -> Check ()
tryEqual x y t msg = case t of
  Equal x' y' -> guardMsg (x == x' && y == y') msg
  _ -> Failure msg

{- Term is application of function type. -}
tryFun :: Term -> Term -> Term -> Check Term
tryFun f xt (Pi a b) =
  if a == xt
  then return b
  else Failure $ "Argument to " ++ show f ++ " must be " ++ show xt ++ ", got " ++ show a ++ "."
tryFun f _ ft = Failure $ "Function " ++ show f ++ " type must be Pi, got " ++ show ft ++ "."


{- Type-check an explicitly typed term, a.k.a check a proof.
   Note that type-checking NatElim and EqElim will
   call reduce on applications to the motive. -}
check :: Term -> Check Term
check = aux V.empty where
  aux :: Context -> Term -> Check Term
  aux ctx = \case
    (App f x) -> do
      ft <- aux ctx f
      xt <- aux ctx x
      result <- tryFun f xt ft
      return $ reduce (subst x result) -- subsitute in dependent type
    (Lam Univ _) -> Failure "This is a first order theory, cannot quantify over types."
    (Lam t1 t2) -> Pi t1 <$> aux (V.cons t1 ctx) t2
    (Pi Univ _) -> Failure "This is a first order theory, cannot quantify over types."
    (Pi t1 t2) -> aux (V.cons t1 ctx) t2 -- Γ,B : U |- Πx:A.B : U
    Var i -> return $ addfree (i + 1) (ctx V.! i) -- update indices in dependent types!
    Nat -> return Univ
    Zero -> return Nat
    Succ -> return $ Pi Nat Nat
    NatElim p p0 pS n -> do
      nt <- aux ctx n ; tryNat nt $ "Expected Nat as last argument to NatElim, got " ++ show nt ++ "."
      pt <- aux ctx p ; tryMotive pt "NatElim"
      p0t <- aux ctx p0
      let expectP0 = reduce (App p Zero)
      guardMsg (p0t == expectP0) $ "natElim base case should prove " ++ show expectP0 ++ ", got " ++ show p0t ++ "."
      pSt <- reduce <$> aux ctx pS
      --let ctx' = V.cons Nat ctx -- bind variable from inductive step
      let ih = reduce (App p (Var 0)) -- type of inductive hypothesis
      --let ctx'' = V.cons ih ctx' -- bind I.H.
      let indRes = reduce (App p (App Succ (Var 1))) -- result of inductive step
      let expectPS = Pi Nat (Pi ih indRes)
      guardMsg (pSt == expectPS) $ "NatElim inductive step should prove " ++ show expectPS ++ ", got " ++ show pSt ++ "."
      return $ reduce (App p n)
    Equal a b -> do
      at <- aux ctx a ; tryNat at $ "LHS of `=` must be Nat, got " ++ show at ++ "."
      bt <- aux ctx b ; tryNat bt $ "RHS of `=` must be Nat, got " ++ show bt ++ "."
      return Univ -- Γ, a : ℕ, b : ℕ |- a = b : *
    Refl -> return $ Pi Nat (Equal (Var 0) (Var 0))
    EqElim p x px y xy -> do
      xt <- aux ctx x ; tryNat xt $ "Second arg of EqElim must be Nat, got " ++ show xt ++ "."
      yt <- aux ctx y ; tryNat yt $ "Fourth arg of EqElim must be Nat, got " ++ show yt ++ "."
      pt <- aux ctx p ; tryMotive pt "EqElim"
      xyt <- reduce <$> aux ctx xy
      tryEqual x y xyt -- has type x = y
        $ "Final argument to EqElim must have type " ++ show x ++ " = " ++ show y ++ ", got " ++ show xyt ++ "."
      pxt <- aux ctx px
      let expectPx = reduce (App p x) -- actually has type P x
      guardMsg (pxt == expectPx) $ "Expected proof of EqElim motive " ++ show expectPx ++ ", got " ++ show pxt ++ "."
      return $ reduce (App p y)
    Univ -> Failure "This is a first order theory, universe has no type."

{- Reduce term to normal form. -}
reduce :: Term -> Term
reduce (App t1 t2) =
  case (reduce t1, reduce t2) of
    -- β reduction
    (Lam _ t1', t2') -> reduce $ subst t2' t1'
    (      t1', t2') -> App t1' t2'
-- TODO: eta reduction
reduce (Lam a t) = Lam a (reduce t)
reduce (Pi t1 t2) = Pi (reduce t1) (reduce t2)
reduce (NatElim p p0 pS n) =
    -- reduce folds recursively
    let (p', p0', pS', n') = (reduce p, reduce p0, reduce pS, reduce n) in
    case n' of
      Zero -> p0'
      App Succ m -> reduce $ App (App pS m) (reduce $ NatElim p' p0' pS' m)
      _ -> NatElim p' p0' pS' n'
reduce (EqElim p x px y xy) = EqElim (reduce p) (reduce x) (reduce px) (reduce y) (reduce xy)
reduce (Equal a b) = Equal (reduce a) (reduce b)
reduce t = t

{- Map over variables of a term
   if depth < index, vs. if depth == index. -}
mapv :: (Int -> Int -> Term) -> (Int -> Int -> Term) -> Term -> Term
mapv f g = aux 0 where
  aux d = \case
    (App t1 t2) -> App (aux d t1) (aux d t2)
    (Lam a t) -> Lam (aux d a) (aux (d + 1) t)
    (Pi a t) -> Pi (aux d a) (aux (d + 1) t)
    v@(Var i)
      | d  < i -> f d i
      | d == i -> g d i
      | otherwise -> v
    (NatElim p p0 pS n) -> NatElim (aux d p) (aux d p0) (aux d pS) (aux d n)
    (Equal a b) -> Equal (aux d a) (aux d b)
    (EqElim p x px y xy) -> EqElim (aux d p) (aux d x) (aux d px) (aux d y) (aux d xy)
    t' -> t'

{- Substitute latest binding with term t. -}
subst :: Term -> Term -> Term
subst t = mapv (\_ i -> Var (i - 1)) (\d _ -> addfree d t)

{- Add k to every free/latest variable index. -}
addfree :: Int -> Term -> Term
addfree k = mapv f f where f _ i = Var (i + k)

{- TODO: "free" with parameter for variable index (not just most recent binding) -}