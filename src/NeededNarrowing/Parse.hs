module NeededNarrowing.Parse (parseTerm, parseTrsFromFile) where

import Data.Char
import Data.Void
import Data.Function
import Data.Maybe
import Control.Monad
import Optics
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char.Lexer qualified as Lexer
import NeededNarrowing

parseTrsFromFile :: FilePath -> IO (TRS String String String)
parseTrsFromFile path = do
  s <- readFile path
  case parse trs path s of
    Left err -> fail (errorBundlePretty err)
    Right r -> return r

parseTerm :: String -> Term String String String
parseTerm = fromJust . parseMaybe term

data RawTree c f x
  = RawLeaf (Term c f x)
  | RawBranch x [(c, [x], RawTree c f x)]
  deriving (Show)

processTree :: Eq x => f -> [x] -> RawTree c f x -> Tree c f x
processTree = \f xs -> go (Op f (Var <$> xs)) where
  go t (RawLeaf t') = Leaf (toPat t, t')
  go t (RawBranch x children) =
    let p = fromJust (findVar x t)
    in Branch p [(c, (xs, go (t & ix p .~ Constr c (Var <$> xs)) child)) | (c, xs, child) <- children]

type RawTRS c f x = [(f, [x], RawTree c f x)]

processTrs :: forall c f x. (Eq f, Eq x) => RawTRS c f x -> TRS c f x
processTrs = map processOp where
  processOp :: (f, [x], RawTree c f x) -> (f, Tree c f x)
  processOp (f, xs, rawTree) = (f, processTree f xs rawTree)

trs :: Parsec Void String (TRS String String String)
trs = processTrs <$> rawTrs

term :: Parsec Void String (Term String String String)
term = parenTerm <|> do
  root <- name
  args <- many (Var <$> name <|> parenTerm)
  return if | isUpper (head root) -> Constr root args
            | null args -> Var root
            | otherwise -> Op root args
  where
    parenTerm = between (key "(") (key ")") term

rawTrs :: Parsec Void String (RawTRS String String String)
rawTrs = space *> many definition <* eof where
  definition = (,,) <$> name <*> many name <*> tree

  tree = key "->" *> (branch <|> leaf)
  branch = RawBranch <$> (key "case" *> name) <*> between (key "{") (key "}") (many case')
  case' = (,,) <$> (key "|" *> name) <*> many name <*> tree
  leaf = RawLeaf <$> term

name = try $ lexeme do
  s <- takeWhile1P Nothing (\c -> not (isSpace c) && c `notElem` ['(', ')', '{', '|', '}'])
  guard (s `notElem` ["->", "case"])
  return s

key = lexeme . string

lexeme = Lexer.lexeme space
space = Lexer.space space1 empty empty
