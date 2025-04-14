module NeededNarrowing.Parse (parseTrsRepFromFile, parseTerm) where

import Data.Function
import Data.Void
import Data.Maybe
import Data.List
import Data.Char
import Control.Monad
import Control.Monad.Writer
import Optics
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as Lexer
import NeededNarrowing

parseTrsRepFromFile :: FilePath -> IO (TRSRep String String String)
parseTrsRepFromFile path = do
  s <- readFile path
  case parse trs path s of
    Left err -> fail (errorBundlePretty err)
    Right r -> return r

parseTerm :: String -> Term String String String
parseTerm = fromJust . parseMaybe term

type RawTRS c f x = [(f, [x], RawTree c f x)]

data RawTree c f x
  = RawLeaf (Term c f x)
  | RawBranch x [(c, [x], RawTree c f x)]
  deriving (Show)

processTrs :: forall c f x. (Ord c, Eq x) => RawTRS c f x -> TRSRep c f x
processTrs rawTrs =
  let (ds, as) = runWriter (traverse processOp rawTrs)
      as' = as & sortOn fst & groupBy ((==) `on` fst) & fmap (nubBy ((==) `on` snd))
  in if all (\xs -> length xs == 1) as'
     then (head <$> as', ds)
     else error "inconsistent constructor arities"
  where
    processOp :: (f, [x], RawTree c f x) -> Writer [(c, Int)] (f, Tree c f x)
    processOp (f, xs, rawTree) = (f,) <$> processTree f xs rawTree

processTree :: Eq x => f -> [x] -> RawTree c f x -> Writer [(c, Int)] (Tree c f x)
processTree = \f xs -> go (Op f (Var <$> xs)) where
  go t (RawLeaf t') = do
    forOf_ subterms t \case
      -- Log the arities of constructor subterms.
      Constr c ts -> tell [(c, length ts)]
      _ -> return ()
    return $ Leaf (t' & vars %~ fromJust . flip findVar t)
  go t (RawBranch x children) = do
    let p = fromJust (findVar x t)
    ts <- forM children \(c, xs, child) -> do
      tell [(c, length xs)]
      children' <- go (t & ix p .~ Constr c (Var <$> xs)) child
      return (c, children')
    return $ Branch p ts

trs :: Parsec Void String (TRSRep String String String)
trs = processTrs <$> rawTrs

rawTrs :: Parsec Void String (RawTRS String String String)
rawTrs = space *> many definition <* eof where
  definition = (,,) <$> name <*> many name <*> tree

  tree = key "->" *> (branch <|> leaf)
  branch = RawBranch <$> (key "case" *> name) <*> between (key "{") (key "}") (many case')
  case' = (,,) <$> (key "|" *> name) <*> many name <*> tree
  leaf = RawLeaf <$> term

term :: Parsec Void String (Term String String String)
term = parenTerm <|> do
  root <- name
  args <- many (Var <$> name <|> parenTerm)
  return if | isUpper (head root) -> Constr root args
            | null args -> Var root
            | otherwise -> Op root args
  where
    parenTerm = between (key "(") (key ")") term

name = try $ lexeme do
  s <- takeWhile1P Nothing \c -> not (isSpace c) && c `notElem` ['(', ')', '{', '|', '}']
  guard (s `notElem` ["->", "case"])
  return s

key = lexeme . string

lexeme = Lexer.lexeme space
space = Lexer.space space1 empty empty
