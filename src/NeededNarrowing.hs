{-# LANGUAGE TemplateHaskell #-}

module NeededNarrowing where

import GHC.Generics
import Data.Coerce
import Data.Void
import Data.Maybe
import Data.List
import Data.Monoid
import Control.Monad
import Control.Monad.Writer
import Optics
import Optics.TH
import Optics.Operators.Unsafe

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
data Term c f x
  = Var x
  | App (Root c f) [Term c f x]
  deriving (Show, Generic)

data Root c f = Constr c | Op f
  deriving (Show, Generic)

-- Traverse a term's variables.
vars :: Traversal (Term c f x) (Term c f x') x x'
vars = traversalVL \focus -> traverseOf vars' (fmap Var . focus)
  
-- Traverse a term's variables, possibly substituting terms for them.
vars' :: Traversal (Term c f x) (Term c f x') x (Term c f x')
vars' = traversalVL go where
  go focus = go' where
    go' (Var x) = focus x
    go' (App r ts) = App r <$> traverse go' ts

-- Pretty-printing terms.
instance (PP c, PP f, PP x) => PP (Term c f x) where
  ppSPrec n = \case
    Var x -> ppSPrec 0 x
    App r ts -> showParen (n > 0)
      (under (coerced @(Endo String)) mconcat
        (intersperse (showString " ") (ppSPrec 0 r : (ppSPrec 1 <$> ts))))
instance (PP c, PP f) => PP (Root c f) where
  ppSPrec n (Constr c) = ppSPrec n c
  ppSPrec n (Op f) = ppSPrec n f

--------------------------------
-- Generating fresh variables --
--------------------------------

-- The Fresh class describes types that know how to generate new elements.
--
-- Law:
--
-- fresh xs `elem` xs = False
class Eq x => Fresh x where
  -- Generate a single new element.
  fresh :: [x] -> x

-- Generate many new elements.
freshN :: Fresh x => Int -> [x] -> [x]
freshN n xs = unfoldr go (n, xs) where
  go (n, xs) | n == 0 = Nothing
             | otherwise = let x = fresh xs in Just (x, (n - 1, x : xs))

-- Generate many variables that do not occur in a given term.
freshIn :: Fresh x => Int -> Term c f x -> [x]
freshIn n = freshN n . toListOf vars

instance Fresh String where
  fresh xs = fromJust . find (`notElem` xs) $ words where
    words = [[]] & iterate (\ws -> [c : w | c <- ['a' .. 'z'], w <- ws]) & concat & tail

--------------------
-- Indexing terms --
--------------------

-- A position is an index that identifies a subterm.  It is represented by a
-- list of indices into immediate subterms.
type Position = [Int]

-- Traverse a term's immediate subterms.
immediateSubterms :: IxTraversal' Position (Term c f x) (Term c f x)
immediateSubterms = itraversalVL \focus -> \case
  Var x -> pure (Var x)
  App r ts -> App r <$> traverse (uncurry focus) ((singleton <$> [0 ..]) `zip` ts)

-- Fold over a term's transitive subterms.
subterms :: IxFold Position (Term c f x) (Term c f x)
subterms = iafolding (Just . ([],)) `isumming`
  (immediateSubterms <%> subterms & reindexed (uncurry (++)))

-- Given a position and a term, we can extract or replace the corresponding
-- subterm.
type instance Index (Term c f x) = Position
type instance IxValue (Term c f x) = Term c f x
instance Ixed (Term c f x) where
  ix [] = singular simple
  ix (i : is) = elementOf immediateSubterms i %> ix is

-- Find the position of a variable in a term.
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
bind s = vars' %~ s

-- Representation of substitutions as association lists.
type SubRep c f x x' = AList x (Term c f x')
type SubRep' c f x = SubRep c f x x

-- Normalize a representation, substituting away "intermediate" variables from
-- each RHS.
--
-- This function assumes that, once a variable occurs as an LHS, it never occurs
-- in any subsequent RHS (or, if it does, that that is a "different" variable
-- that just happens to have the same name).
normalize :: Eq x => SubRep' c f x -> SubRep' c f x
normalize s = s & foldl' go [] & reverse where
  go acc s@(x, t) = s : (acc & mapped % _2 %~ bind (sub [s]))

-- Lift a representation to a substitution.
sub :: Eq x => SubRep' c f x -> Sub' c f x
sub s x = fromMaybe (Var x) . alistGet x . normalize $ s

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

-- Rewrite at a position in a term.
rewriteAt :: Rule c f -> Position -> Term c f x -> Term c f x
rewriteAt r p t = bind (\p' -> t ^?! ix (p ++ p')) r

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
  deriving (Show)

----------------------------
-- Term rewriting systems --
----------------------------

-- A term-rewriting system (TRS) is, for our purposes, a mapping from function
-- symbols to definitional trees.
--
-- A TRS must also know the arity of each constructor symbol.
data TRS c f x = TRS { _arity :: c -> Int
                     , _defn :: f -> Tree c f x
                     }
makeLenses ''TRS

-- Representation of a TRS as a pair of association lists.
type TRSRep c f x = (AList c Int, AList f (Tree c f x))

-- Lift a representation to a TRS.
appTrsRep :: (Eq c, Eq f) => TRSRep c f x -> TRS c f x
appTrsRep (a, d) = TRS { _arity = \c -> fromJust . alistGet c $ a
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

-- Given a term (in a TRS), compute all possible ways that it could be narrowed.
narrowings' :: forall c f x. (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [(Term c f x, SubRep c f x x)]
narrowings' trs = \case
  t@(App (Op f) ts) -> runWriterT (go ((trs ^. defn) f) [] t)
  _ -> []
  where
    go :: Tree c f x -> Position -> Term c f x -> WriterT (SubRep' c f x) [] (Term c f x)
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
    -- substitutions necessary to perform the narrowing.
    --
    -- The focusing position p identifies the subterm of t that we are
    -- inspecting.  We need to keep track of this because, when we find that the
    -- subterm at the inductive position is operation-rooted, we must
    -- recursively narrow that operation.
    --
    -- We need to keep the entire term t around because any free variables that
    -- we instantiate must be instantiated everywhere they occur in t, not just
    -- in the subterm that we are inspecting.
    go (Leaf r) p t = return (rewriteAt r p t)
    go (Branch ip children) p t =
      -- ip is the inductive position.  p is the position that we are focusing.
      -- p' is the inductive position relative to p.
      let p' = p ++ ip
          -- u is the subterm of t at position p'.
          u = t ^?! ix p'
      in case u of
        App (Constr c) ts -> case alistGet c children of
          -- The subterm at the inductive position is a constructor application.
          -- We need to continue with the child case corresponding to that
          -- constructor.  If there isn't one, we fail.
          Nothing -> mzero
          Just child -> go child p t
        Var x -> do
          -- The subterm at the inductive position is a variable.  We
          -- instantiate that variable with each possible constructor case and
          -- continue.
          (c, child) <- lift children
          let n = (trs ^. arity) c
          -- Generate fresh variables for the constructor arguments.
          let newVars = freshIn n t
          let s = [(x, App (Constr c) (Var <$> newVars))]
          tell s
          let t' = bind (sub s) t
          go child p t'
        App (Op f) _ ->
          -- The subterm at the inductive position is a function application.
          -- We narrow it recursively.  We also need to focus in on the
          -- inductive position.
          go ((trs ^. defn) f) ip t

narrowings :: forall c f x. (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [Term c f x]
narrowings trs t = fst <$> narrowings' trs t
