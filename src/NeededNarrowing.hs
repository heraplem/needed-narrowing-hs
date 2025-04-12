module NeededNarrowing where

import Data.Coerce
import Data.Void
import Data.Maybe
import Data.List
import Data.Monoid
import Control.Monad
import Control.Monad.Writer
import Optics
import Optics.Operators.Unsafe

-----------------------
-- Association lists --
-----------------------

type AList k v = [(k, v)]

alistGet :: Eq k => k -> AList k v -> Maybe v
alistGet k = fmap snd . find ((k ==) . fst)

-----------
-- Terms --
-----------

-- Terms over:
--
-- + a type c of constructor symbols;
--
-- + a type f of function symbols;
--
-- + a type x of variables.

data Term c f x
  = Constr c [Term c f x]
  | Op f [Term c f x]
  | Var x
  deriving (Show)

-- Get or set a term's immediate subterms (if it has any).

immediateSubterms :: AffineTraversal' (Term c f x) [Term c f x]
immediateSubterms = atraversal get set where
  get (Constr _ ts) = Right ts
  get (Op _ ts) = Right ts
  get t = Left t

  set (Constr c ts) ts' = Constr c ts'
  set (Op f ts) ts' = Op f ts'
  set t _ = t

--------------------
-- Indexing terms --
--------------------

-- A position is an index that identifies a subterm.  It is represented by a
-- list of indices into immediate subterms.

type Position = [Int]

-- Given a position and a term, we can extract or replace the corresponding
-- subterm.

type instance Index (Term c f x) = Position
type instance IxValue (Term c f x) = Term c f x

instance Ixed (Term c f x) where
  ix [] = atraversal Right (const id)
  ix (i : is) = immediateSubterms % ix i % ix is

-- We can also look for a variable in a term.

findVar :: Eq x => x -> Term c f x -> Maybe Position
findVar x = go where
  go (Var x') | x' == x = Just []
              | otherwise = Nothing
  go (Constr _ ts) = go' ts
  go (Op _ ts) = go' ts

  go' ts = ts & zipWith (\i t -> (i:) <$> go t) [0..] &
    under (coerced @(Alt Maybe [Int])) mconcat

-------------------
-- Substitutions --
-------------------

type Sub c f x = AList x (Term c f x)

-- Substitute a single variable.

sub :: Eq x => Sub c f x -> x -> Term c f x
sub s x = fromMaybe (Var x) . alistGet x $ s

-- Action of substitutions on terms.

bind :: Eq x => Sub c f x -> Term c f x -> Term c f x
bind s = go where
  go (Constr c ts) = Constr c (go <$> ts)
  go (Op f ts) = Op f (go <$> ts)
  go (Var x) = sub s x

--------------
-- Patterns --
--------------

-- A pattern is, morally, a term of the form f(t1, ..., tn), where t1, ..., tn
-- do not contain any function symbols.
--
-- In our system, a pattern always occurs in the leaf of a definitional tree,
-- which (to make a long story short) means that we do not actually need to
-- remember the root function symbol or any constructor symbols.  We only need
-- to know the pattern variables and their positions.

type Pat x = [Term () Void x]

-- Match a pattern against a term to produce a substitution that maps pattern
-- variables to their corresponding subterms.
--
-- We assume that the pattern is linear.

match :: Pat x -> Term c f x -> Sub c f x
match = \ps (Op _ ts) -> concatMap (uncurry go) (zip ps ts) where
  go (Var x) t' = [(x, t')]
  go (Constr _ ts) (Constr c' ts') = concatMap (uncurry go) (zip ts ts')

-- Convert a term to a pattern.

toPat :: Term c f x -> Pat x
toPat = \(Op _ ts) -> go <$> ts where
  go (Var x) = Var x
  go (Constr _ ts) = Constr () (go <$> ts)

-------------------
-- Rewrite rules --
-------------------

-- A rewrite rule is a pair (lhs, rhs) of a left-hand side pattern and a
-- corresponding right-hand side term.

type Rule c f x = (Pat x, Term c f x)

-- Action of rewrite rules on terms.

rewrite :: Eq x => Rule c f x -> Term c f x -> Term c f x
rewrite (p, t') t = bind (match p t) t'

-- Rewriting at a subterm.  (We could simulate this by generating a pattern with
-- free variables everywhere except at the rewriting position, but then we would
-- have to decide how to generate free variables.)

rewriteAt :: Eq x => Rule c f x -> Position -> Term c f x -> Term c f x
rewriteAt r p = ix p %~ rewrite r

------------------------
-- Definitional trees --
------------------------

-- A definitional tree is one of:
--
-- + a branch, which specifies a position to scrutinize (the "inductive
--   position") and then a list of possible cases (for the scrutinized subterm)
--   and associated child trees;
--
-- + a leaf, which specifies a rewrite rule.
--
-- You can think of a definitional tree as an "operationalized" definition by
-- pattern-matching.  It tells you the order in which to match subpatterns.

data Tree c f x
  = Leaf (Rule c f x)
  | Branch Position (AList c ([x], Tree c f x))
  deriving (Show)

----------------------------
-- Term rewriting systems --
----------------------------

type TRS c f x = AList f (Tree c f x)

trsGet :: Eq f => f -> TRS c f x -> Tree c f x
trsGet f = fromJust . alistGet f

---------------
-- Narrowing --
---------------

-- Given a term (in a TRS), we can compute all possible narrowing steps that
-- could apply to it.

narrowings' :: forall c f x. (Eq c, Eq f, Eq x) => TRS c f x -> Term c f x -> [(Term c f x, Sub c f x)]
narrowings' trs = \case
  t@(Op f ts) -> runWriterT (go (trsGet f trs) [] t)
  _ -> []
  where
    -- This is the main loop.
    --
    -- We are given:
    --
    -- + the definitional tree for an operation f;
    --
    -- + a position p that we are "focusing"; and
    --
    -- + a term t (rooted by f) that we are inspecting.
    --
    -- We return a list of possible terms that t could narrow to, along with the
    -- necessary substitutions.
    --
    -- The focusing position p identifies the subterm of t that we are
    -- inspecting.  We need to keep track of this because, when we find that the
    -- subterm at the inductive position is operation-rooted, we must
    -- recursively narrow that subterm.
    --
    -- We need to keep the entire term t around because any free variables that
    -- we instantiate must be instantiated everywhere they occur in t, not just
    -- in the subterm that we are inspecting.
    go :: Tree c f x -> Position -> Term c f x -> WriterT (Sub c f x) [] (Term c f x)
    go (Leaf r) p t = return (rewriteAt r p t)
    go (Branch ip children) p t =
         -- ip is the inductive position.  p is the position that we are
         -- focusing.  p' is the subterm at the inductive position relative to
         -- p.
      let p' = p ++ ip
          -- u is the subterm of t at position p'
          u = t ^?! ix p'
      in case u of
        Constr c ts -> case alistGet c children of
          -- The subterm at the inductive position is a constructor.  We need to
          -- continue with the child case corresponding to that constructor.  If
          -- there isn't one, we fail.
          Nothing -> mzero
          Just (_, child) -> go child p t
        Var x -> do
          -- The subterm at the inductive position is a variable.  We
          -- instantiate that variable with each possible constructor case and
          -- continue.
          (c, (xs, child)) <- lift children
          let s = [(x, Constr c (Var <$> xs))]
          tell s
          let t' = bind s t
          go child p t'
        Op f _ ->
          -- The subterm at the inductive position is a function application.
          -- We narrow it recursively.
          go (trsGet f trs) p' u

narrowings :: forall c f x. (Eq c, Eq f, Eq x) => TRS c f x -> Term c f x -> [Term c f x]
narrowings trs t = fst <$> narrowings' trs t
