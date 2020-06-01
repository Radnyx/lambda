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

{-# LANGUAGE LambdaCase, BlockArguments #-}

module LF (Term(..), check, reduce) where

import qualified Data.Vector as V
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
 | Refl Term
 | EqElim Term Term Term Term Term
 | Univ
 deriving (Eq, Show, Ord)

{- TODO: show Terms, write "->" if var is free in type! -}



{- Term is ℕ. -}
tryNat :: Alternative f => Term -> f ()
tryNat = \case { Nat -> pure () ; _ -> empty }

{- Term is Πx:A.B. -}
tryPi :: Alternative f => Term -> f (Term, Term)
tryPi = \case { Pi t1 t2 -> pure (t1, t2) ; _ -> empty }

{- Term is Πx:ℕ.*. -}
tryMotive :: MonadPlus m => Term -> m ()
tryMotive t = do
  (t1, t2) <- tryPi t ; tryNat t1 ; guard (t2 == Univ)
  return ()

{- Term is x = y. -}
tryEqual :: Alternative m => Term -> Term -> Term -> m ()
tryEqual x y = \case
  Equal x' y' -> guard (x == x' && y == y')
  _ -> empty

{- Term is application of function type. -}
tryFun :: MonadPlus m => Term -> Term -> m Term
tryFun xt = \case
  Pi a b -> guard (a == xt) >> return b
  _ -> empty


{- Type-check an explicitly typed term, a.k.a check a proof.
   Note that type-checking NatElim and EqElim will
   call reduce on applications to the motive. -}
check :: Term -> Maybe Term
check = aux V.empty where
  aux :: Context -> Term -> Maybe Term
  aux ctx = \case
    (App f x) -> do
      ft <- aux ctx f
      xt <- aux ctx x
      tryFun xt ft
    (Lam Univ _) -> Nothing -- first order theory
    (Lam t1 t2) -> Pi t1 <$> aux (V.cons t1 ctx) t2
    (Pi Univ _) -> Nothing -- first order theory
    (Pi t1 t2) -> aux (V.cons t1 ctx) t2 -- Γ,B : U |- Πx:A.B : U
    Var i -> return $ ctx V.! i
    Nat -> return Univ
    Zero -> return Nat
    Succ -> return $ Pi Nat Nat
    NatElim p p0 pS n -> do
      nt <- aux ctx n ; tryNat nt
      pt <- aux ctx p ; tryMotive pt
      p0t <- aux ctx p0
      guard (p0t == reduce (App p Zero)) -- actually has type P 0
      pSt <- aux ctx pS
      --let ctx' = V.cons Nat ctx -- bind variable from inductive step
      let ih = reduce (App p (Var 0)) -- type of inductive hypothesis
      --let ctx'' = V.cons ih ctx' -- bind I.H.
      let indRes = reduce (App p (App Succ (Var 1))) -- result of inductive step
      guard (pSt == Pi Nat (Pi ih indRes))
      return $ reduce (App p n)
    Equal a b -> do
      at <- aux ctx a ; tryNat at
      bt <- aux ctx b ; tryNat bt
      return Univ -- Γ, a : ℕ, b : ℕ |- a = b : *
    Refl -> return $ Pi Nat (Equal (Var 0) (Var 0)) do
    EqElim p x px y xy -> do
      xt <- aux ctx x ; tryNat xt
      yt <- aux ctx y ; tryNat yt
      pt <- aux ctx p ; tryMotive pt
      xyt <- aux ctx xy ; tryEqual x y xyt -- has type x = y
      pxt <- aux ctx px
      guard (pxt == reduce (App p x)) -- actually has type P x
      return $ reduce (App p y)
    Univ -> Nothing -- only one Martin Löf universe, untypable

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
reduce t = t

{- Map over variables of a term
   if depth < index, vs. if depth == index. -}
mapv :: (Int -> Int -> Term) -> (Int -> Int -> Term) -> Term -> Term
mapv f g = aux 0 where
  aux d = \case
    (App t1 t2) -> App (aux d t1) (aux d t2)
    (Lam a t') -> Lam a (aux (d + 1) t')
    (Pi a t') -> Pi a (aux (d + 1) t')
    v@(Var i)
      | d  < i -> f d i
      | d == i -> g d i
      | otherwise -> v
    (NatElim p p0 pS n) -> NatElim (aux d p) (aux d p0) (aux d pS) (aux d n)
    (Equal a b) -> Equal (aux d a) (aux d b)
    (Refl a) -> Refl (aux d a)
    (EqElim p x px y xy) -> EqElim (aux d p) (aux d x) (aux d px) (aux d y) (aux d xy)
    t' -> t'

{- Substitute latest binding with term t. -}
subst :: Term -> Term -> Term
subst t = mapv (\_ i -> Var (i - 1)) (\d _ -> addfree d t)

{- Add k to every free/latest variable index. -}
addfree :: Int -> Term -> Term
addfree k = mapv f f where f _ i = Var (i + k)

{- TODO: "free" with parameter for variable index (not just most recent binding) -}