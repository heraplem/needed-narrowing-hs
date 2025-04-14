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
  | Constr c [Term c f x]
  | Op f [Term c f x]
  deriving (Show, Generic)

-- Traverse a term's immediate subterms.
immediateSubterms :: Traversal' (Term c f x) (Term c f x)
immediateSubterms = gplate

-- Fold over a term's transitive subterms.
subterms :: Fold (Term c f x) (Term c f x)
subterms = cosmosOf immediateSubterms

-- Traverse a term's variables.
vars :: Traversal (Term c f x) (Term c f x') x x'
vars = traversalVL \focus -> traverseOf vars' (fmap Var . focus)

-- Traverse a term's variables, possibly substituting them with terms.
vars' :: Traversal (Term c f x) (Term c f x') x (Term c f x')
vars' = traversalVL go where
  go focus = go' where
    go' (Var x) = focus x
    go' (Constr c ts) = Constr c <$> traverse go' ts
    go' (Op f ts) = Op f <$> traverse go' ts

instance (PP c, PP f, PP x) => PP (Term c f x) where
  ppSPrec n = \case
    Var x -> ppSPrec 0 x
    Constr c ts -> ppApp c ts
    Op f ts -> ppApp f ts
    where
      ppApp :: PP a => a -> [Term c f x] -> ShowS
      ppApp s ts = showParen (n > 0)
        (under (coerced @(Endo String)) mconcat
         (intersperse (showString " ") (ppSPrec 0 s : (ppSPrec 1 <$> ts))))

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
    words = [[]] & iterate (\ws -> [c : w | c <- ['a'..'z'], w <- ws]) & concat & tail

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
  ix [] = singular simple
  ix (i : is) = elementOf immediateSubterms i %> ix is

-- Find the position of a variable in a term.
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

-- A substitution is a mapping from variables to terms.  In general, the
-- variable types may differ.
type Sub c f x x' = x -> Term c f x'

-- Apply a substitution to a term.
bind :: Sub c f x x' -> Term c f x -> Term c f x'
bind s = vars' %~ s

-- Representation of a substitution as an association list.
type SubRep c f x x' = AList x (Term c f x')

-- Lift a representation to a substitution.
appSubRep :: Eq x => SubRep c f x x -> Sub c f x x
appSubRep s x = fromMaybe (Var x) . alistGet x $ s

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

---------------
-- Narrowing --
---------------

-- Given a term (in a TRS), compute all possible ways that it could be narrowed.
narrowings' :: forall c f x. (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [(Term c f x, SubRep c f x x)]
narrowings' trs = \case
  t@(Op f ts) -> runWriterT (go ((trs ^. defn) f) [] t)
  _ -> []
  where
    go :: Tree c f x -> Position -> Term c f x -> WriterT (SubRep c f x x) [] (Term c f x)
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
          -- u is the subterm of t at position p'
          u = t ^?! ix p'
      in case u of
        Constr c ts -> case alistGet c children of
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
          let s = [(x, Constr c (Var <$> newVars))]
          tell s
          let t' = bind (appSubRep s) t
          go child p t'
        Op f _ ->
          -- The subterm at the inductive position is a function application.
          -- We narrow it recursively.  We also need to focus in on the
          -- inductive position.
          go ((trs ^. defn) f) p' u

narrowings :: forall c f x. (Eq c, Eq f, Fresh x) => TRS c f x -> Term c f x -> [Term c f x]
narrowings trs t = fst <$> narrowings' trs t
