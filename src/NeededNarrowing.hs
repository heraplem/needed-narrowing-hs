{-# LANGUAGE AllowAmbiguousTypes, TemplateHaskell #-}

module NeededNarrowing where

import Data.Coerce
import Data.Char
import Data.Void
import Data.Maybe
import Data.List
import Data.Monoid
import Data.Foldable
import Control.Monad
import Control.Monad.State
import Control.Monad.RWS
import Optics hiding (uncons)
import Optics.TH
import Optics.Operators.Unsafe
import Optics.State.Operators
import Optics.View

-----------------------
-- Association lists --
-----------------------

type AList k v = [(k, v)]

alistGet :: Eq k => k -> AList k v -> Maybe v
alistGet k = fmap snd . find ((k ==) . fst)

---------------------
-- Pretty-printing --
---------------------

class PP a where
  pp :: a -> String
  pp x = ppSPrec 0 x ""

  ppSPrec :: Int -> a -> ShowS
  ppSPrec _ x = showString (pp x)

ppS :: PP a => a -> ShowS
ppS = ppSPrec 0

instance PP String where
  ppSPrec _ = showString

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
--
-- Note that the Functor instance for terms maps over variables.  This is the
-- sensible choice: acting on variables is a common operation, whereas I have
-- not yet run into a situation where I needed to act on constructor or function
-- symbols.
data Term c f x
  = Var x
  | App (Root c f) [Term c f x]
  deriving (Eq, Ord, Read, Show, Functor, Traversable, Foldable)

data Root c f = Constr c | Op f
  deriving (Eq, Ord, Read, Show)

instance Applicative (Term c f) where
  pure = Var
  (<*>) = ap

instance Monad (Term c f) where
  (>>=) = flip go where
    go k = go' where
      go' (Var x) = k x
      go' (App r ts) = App r (go' <$> ts)

isVar :: Term c f x -> Bool
isVar (Var _) = True
isVar _ = False

isConstrRooted :: Term c f x -> Bool
isConstrRooted (App (Constr _) _) = True
isConstrRooted _ = False

isOpRooted :: Term c f x -> Bool
isOpRooted (App (Op _) _) = True
isOpRooted _ = False

-- Pretty-print terms.
instance (PP c, PP f, PP x) => PP (Term c f x) where
  ppSPrec n = \case
    Var x -> ppS x
    App r ts -> showParen (n > 0 && not (null ts))
      (under (coerced @(Endo String))
       mconcat
        (intersperse (showString " ") (ppS r : (ppSPrec 1 <$> ts))))
instance (PP c, PP f) => PP (Root c f) where
  ppSPrec n (Constr c) = ppSPrec n c
  ppSPrec n (Op f) = ppSPrec n f

--------------------------------
-- Generating fresh variables --
--------------------------------

-- The Fresh class describes types that know how to generate new elements.
class Eq x => Fresh x where
  type Source x
  allFresh :: Source x
  fresh :: Source x -> (x, Source x)
  stale :: x -> Source x -> Source x

-- Generate many new elements.
freshN :: Fresh x => Int -> Source x -> ([x], Source x)
freshN n = runState (replicateM n . state $ fresh)

-- Stale many elements.
staleN :: Fresh x => [x] -> Source x -> Source x
staleN = flip (foldr stale)

-- Stale all variables in a term.
staleTerm :: Fresh x => Term c f x -> Source x -> Source x
staleTerm t = staleN (toList t)

instance Fresh String where
  type Source String = [(Int, Maybe String)]

  allFresh = [[]] & iterate buildWords & concat & map Just & zip [0..] & tail where
    buildWords ws = [c : w | c <- ['a'..'z'], w <- ws]

  fresh s = s & dropWhile (isNothing . snd) & uncons & fromJust & _1 %~ fromJust . snd

  stale x xs
    | all isAsciiLower x = xs & ix (end - start) % _2 .~ Nothing
    | otherwise = xs
   where
     start = fst (head xs)
     end = sum [(26 ^ i) * (ord c - ord 'a' + 1) | (i, c) <- [0..] `zip` reverse x]

--------------------
-- Indexing terms --
--------------------

-- A position is an index that identifies a subterm.  It is represented by a
-- list of indices into immediate subterms.
type Position = [Int]

-- Traverse a term's immediate subterms.
immediateSubterms :: IxTraversal' Position (Term c f x) (Term c f x)
immediateSubterms = itraversalVL \focus -> \case
  App r ts -> App r <$> traverse (uncurry focus) ((singleton <$> [0..]) `zip` ts)
  t -> pure t

-- Fold over a term's transitive subterms.
subterms :: IxFold Position (Term c f x) (Term c f x)
subterms = iafolding (Just . ([],)) `isumming`
  (immediateSubterms <%> subterms & reindexed (uncurry (++)))

-- Given a position and a term, extract or replace the corresponding subterm.
type instance Index (Term c f x) = Position
type instance IxValue (Term c f x) = Term c f x
instance Ixed (Term c f x) where
  ix [] = singular simple
  ix (i : is) = elementOf immediateSubterms i %> ix is

-- Find the (first) position of a variable in a term.
findVar :: Eq x => x -> Term c f x -> Maybe Position
findVar x = fmap fst . ifindOf subterms \_ -> \case
  Var x' -> x' == x
  _ -> False

-------------------
-- Substitutions --
-------------------

-- A substitution is a mapping from some domain to terms.  Most commonly, the
-- domain is the type of variables.
type Sub c f x x' = x -> Term c f x'
type Sub' c f x = Sub c f x x

-- Apply a substitution to a term.
bind :: Sub c f x x' -> Term c f x -> Term c f x'
bind = (=<<)

-- Representation of substitutions as association lists.
type SubRep c f x = AList x (Term c f x)

-- Lift a representation to a substitution.
sub :: Eq x => SubRep c f x -> Sub' c f x
sub s x = fromMaybe (Var x) . alistGet x . normalize $ s

-- Normalize a representation, substituting away "intermediate" variables from
-- each RHS.
--
-- This function assumes that, once a variable occurs as an LHS, it never occurs
-- in any subsequent RHS (or, if it does, that that is a "different" variable
-- that just happens to have the same name).
normalize :: Eq x => SubRep c f x -> SubRep c f x
normalize s = s & foldl' go [] & reverse where
  go acc s = s : (acc & mapped % _2 %~ bind (sub [s]))

-------------------
-- Rewrite rules --
-------------------

-- Morally, a rewrite rule is a pair p -> t, where p is a pattern and t is a
-- term with variables drawn from p.  However, in this system, a rewrite rule
-- always occurs as the leaf of a definitional tree, which (to make a long story
-- short) means that the pattern can always be inferred from context.
-- Therefore, we represent a rewrite rule purely by its right-hand side.  Also,
-- instead of explicit variable names, we use indices into the term that is
-- being rewritten.
type Rule c f = Term c f Position

-- Rewrite a term.
rewrite :: Rule c f -> Term c f x -> Term c f x
rewrite r t = bind (\p -> t ^?! ix p) r

------------------------
-- Definitional trees --
------------------------

-- A definitional tree is one of the following.

-- + A leaf, which specifies a rewrite rule.
--
-- + A branch, which specifies a position to scrutinize (the "inductive
--   position") and then a list of possible cases.  Each case consists of a
--   constructor symbol, the arity of that constructor, and a child tree.
--
-- You can think of a definitional tree as an "operationalized" definition by
-- pattern-matching.  It tells you the order in which to match subpatterns.

data Tree c f x
  = Leaf (Rule c f)
  | Branch Position (AList c (Tree c f x))
  deriving (Eq, Ord, Read, Show)

----------------------------
-- Term rewriting systems --
----------------------------

-- A term-rewriting system (TRS) is, for our purposes, a mapping from function
-- symbols to definitional trees.
--
-- A TRS must also know the arity of each constructor symbol.
data TRS c f x = TRS
  { _arity :: c -> Int
  , _defn :: f -> Tree c f x
  }
makeLenses ''TRS

-- Representation of a TRS as a pair of association lists.
type TRSRep c f x = (AList c Int, AList f (Tree c f x))

-- Lift a representation to a TRS.
appTrsRep :: (Eq c, Eq f) => TRSRep c f x -> TRS c f x
appTrsRep (a, d) = TRS
  { _arity = \c -> fromJust . alistGet c $ a
  , _defn = \f -> fromJust . alistGet f $ d
  }

-- Augment a TRS representation with rules for equality.
augment :: c -> f -> f -> TRSRep c f x -> TRSRep c f x
augment success eq conj (as, ds) = (as', ds') where
  as' = (success, 0) : as
  ds' =
    (conj, Branch [0] [(success, Branch [1] [(success, Leaf successT)])]) :
    (eq, Branch [0] [
        (c, Branch [1]
          [(c, Leaf (foldr (\i t -> App (Op conj) [App (Op eq) [Var [0, i], Var [1, i]], t]) successT [0 .. n - 1]))]) |
          (c, n) <- as]) :
    ds
  successT = App (Constr success) []

---------------
-- Narrowing --
---------------

data NarrowingEnv c f x = NarrowingEnv
  { _trs :: TRS c f x
  , _pos :: Position
  }
makeLenses ''NarrowingEnv

initialEnv :: TRS c f x -> NarrowingEnv c f x
initialEnv trs = NarrowingEnv
  { _trs = trs
  , _pos = []
  }

data NarrowingState c f x = NarrowingState
  { _term :: Term c f x
  , _vars :: Source x
  }
makeLenses ''NarrowingState

initialState :: forall c f x. Fresh x => Term c f x -> NarrowingState c f x
initialState t = NarrowingState
  { _term = t
  , _vars = allFresh @x & staleTerm t
  }

type Narrow c f x a = RWST (NarrowingEnv c f x) (SubRep c f x) (NarrowingState c f x) [] a

-- Get the definitional tree of a function symbol.
defnOf :: f -> Narrow c f x (Tree c f x)
defnOf f = gviews (trs % defn) ($ f)

-- Get the arity of a constructor symbol.
arityOf :: c -> Narrow c f x Int
arityOf c = gviews (trs % arity) ($ c)

-- Zoom in on a given position (relative to the current focus) and execute an
-- action.
zoomed :: Position -> Narrow c f x a -> Narrow c f x a
zoomed p = local (pos %~ (++ p))

-- Get the focused subterm.
focusedSubterm :: Narrow c f x (Term c f x)
focusedSubterm = do
  p <- gview pos
  t <- use term
  return (t ^?! ix p)

-- Instantiate a variable to an application of a constructor.
instantiate :: Fresh x => c -> x -> Narrow c f x ()
instantiate c x = do
    a <- arityOf c
    newVars <- state (passthrough vars (freshN a))
    substitute x (App (Constr c) (Var <$> newVars))

-- Substitute one variable in the entire term.
substitute :: Eq x => x -> Term c f x -> Narrow c f x ()
substitute x t = do
  let s = [(x, t)]
  tell s
  modifying term (bind (sub s))

-- Apply a rewrite rule to the focused subterm.
rewriteBy :: Rule c f -> Narrow c f x ()
rewriteBy r = do
  p <- gview pos
  modifying (term % ix p) (rewrite r)

-- Apply one narrowing step to a term.
narrow :: (Eq c, Eq f, Fresh x) => Narrow c f x ()
narrow = focusedSubterm >>= \case
  App (Op f) _ -> narrowOf f
  _ -> mzero

-- Find the leftmost operation-rooted subterm and apply a narrowing step there.
narrow' :: (Eq c, Eq f, Fresh x) => Narrow c f x ()
narrow' = do
  t <- focusedSubterm
  case ifindOf subterms (const isOpRooted) t of
    Nothing -> mzero
    Just (p, _) -> zoomed p narrow

-- Narrow an application of a given function.
narrowOf :: (Eq c, Eq f, Fresh x) => f -> Narrow c f x ()
narrowOf f = narrowBy =<< defnOf f

-- Narrow according to a given definitional tree.
narrowBy :: (Eq c, Eq f, Fresh x) => Tree c f x -> Narrow c f x ()
narrowBy (Leaf r) =
  rewriteBy r
narrowBy (Branch p ds) =
  zoomed p focusedSubterm >>= \case
    App (Constr c) _ ->
      maybe mzero narrowBy (alistGet c ds)
    Var x -> do
      (c, d) <- lift ds
      instantiate c x
      narrowBy d
    App (Op f) _ ->
      zoomed p (narrowOf f)

narrowings :: (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [Term c f x]
narrowings trs t = runRWST narrow (initialEnv trs) (initialState t) <&> view (_2 % term)

narrowings' :: (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [Term c f x]
narrowings' trs t = runRWST narrow' (initialEnv trs) (initialState t) <&> view (_2 % term)

data ETree a = ETree a [ETree a]
  deriving (Eq, Ord, Read, Show, Functor, Traversable, Foldable)

eval :: (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> ETree (Term c f x)
eval trs t = ETree t (eval trs <$> narrowings trs t)

eval' :: (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> ETree (Term c f x)
eval' trs t = ETree t (eval' trs <$> narrowings' trs t)

instance PP a => PP (ETree a) where
  ppSPrec _ = go 0 where
    go n (ETree x ts) =
      ppS (concat (replicate (n - 1) "│ ")) .
      ppS (if n > 0 then "├ " else "") .
      ppS x .
      ppS "\n" .
      appEndo (foldMap (Endo . go (n + 1)) ts)
