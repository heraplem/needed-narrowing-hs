module NeededNarrowing where

import Data.Void
import Data.List
import Control.Monad
import Control.Monad.Writer
import Optics
import Optics.Operators.Unsafe

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

immediateSubterms :: AffineTraversal' (Term c f x) [Term c f x]
immediateSubterms = atraversal get set where
  get (Constr _ ts) = Right ts
  get (Op _ ts) = Right ts
  get t = Left t

  set (Constr c ts) ts' = Constr c ts'
  set (Op f ts) ts' = Op f ts'
  set t _ = t

-------------------
-- Substitutions --
-------------------

-- A substitution is a list that associates terms to variables.
--
-- We could just represent a substitution as a function from variables to terms,
-- but narrowing will compute a substitution as an output, and we want to be
-- able to inspect it.

type Sub c f x = [(x, Term c f x)]

-- Substitute a single variable.

sub :: Eq x => Sub c f x -> x -> Term c f x
sub s x = s & find ((x == ) . fst) & maybe (Var x) snd

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
match ps (Op _ ts) = concatMap (uncurry go) (zip ps ts) where
  go (Var x) t' = [(x, t')]
  go (Constr _ ts) (Constr c' ts') = concatMap (uncurry go) (zip ts ts')

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
-- free variables, but then we would have to decide how to generate free
-- variables.)

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
-- You can think of a definitional tree as an "operationalized" pattern (in the
-- general sense of the term "pattern").  It tells you the order in which to
-- match subpatterns.

data Tree c f x
  = Leaf (Rule c f x)
  | Branch Position [(c, [Term c f x], Tree c f x)]

----------------------------
-- Term rewriting systems --
----------------------------

-- For our purposes, a term rewriting system is just a function that associates
-- to each function symbol a definitional tree.

type TRS c f x = f -> Tree c f x

---------------
-- Narrowing --
---------------

-- A narrowing step is a substitution followed by a rewrite rule at a certain
-- position.  The purpose of the substitution is to instantiate free variables
-- in order to make the rewrite rule applicable.

type NarrowingStep c f x = (Sub c f x, Rule c f x, Position)

-- Narrowing steps act on terms in the obvious way.

narrow :: Eq x => NarrowingStep c f x -> Term c f x -> Term c f x
narrow (s, r, p) = rewriteAt r p . bind s

-- Now, given a term (in a TRS), we can compute all possible narrowing steps
-- that could apply to it.

narrowings :: forall c f x. (Eq c, Eq x) => TRS c f x -> Term c f x -> [NarrowingStep c f x]
narrowings trs = \case
  t@(Op f ts) -> runWriterT (go (trs f) t) & fmap \(r, (s, p)) -> (s, r, p)
  _ -> []
  where
    -- This is the main loop.  We are given a definitional tree for some
    -- operation `f` and a term `t` that is rooted by `f`.  We return a list of
    -- all possible rewrite rules that could be applied to `t`.  Along the way,
    -- we accumulate the position at which the rule must be applied, as well as
    -- the substitution necessary to make the rule applicable.
    go :: Tree c f x -> Term c f x -> WriterT (Sub c f x, Position) [] (Rule c f x)
    go (Leaf r) _ = return r
    go (Branch p cs) t =
      -- `u` is the subterm of `t` at position `p`.
      let u = t ^?! ix p
      in case u of
        Constr c ts -> case find (\(c', _, _) -> c' == c) cs of
          -- The subterm at `p` is a constructor application.  If there is a
          -- child node with that constructor, continue; otherwise, fail.
          Nothing -> mzero
          Just (_, _, child) -> go child t
        Var x -> do
          -- The subterm at `p` is a variable `x`.  For each child node:
          (c, ts, child) <- lift cs
          -- Construct a singleton substitution `s` that maps `x` to that
          -- constructor application.
          let s = [(x, Constr c ts)]
          -- Append that substitution to the output.
          tell (s, [])
          -- Also, apply it to the term that we are narrowing.
          let t' = bind s t
          -- Continue.
          go child t'
        Op f _ -> do
          -- The subterm at `p` is an application of a function `f`.  We are
          -- going to have to apply a narrowing step to `f`.
          --
          -- The resulting rewrite rule will have to be applied at position `p`.
          tell ([], p)
          -- Continue.
          go (trs f) u

-- Finally, given a term in a TRS, we can compute all possible narrowing steps
-- and immediately apply them.  This is essentially a small-step operational
-- semantics for the TRS.

narrows :: (Eq c, Eq x) => TRS c f x -> Term c f x -> [Term c f x]
narrows trs t = flip narrow t <$> narrowings trs t
