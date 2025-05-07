{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

import Control.Comonad.Cofree (Cofree (..), unwrap)
import Control.Lens.Plated (Plated (..))
import Control.Monad (void)
import Control.Monad.State (State)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Functor (($>))
import Data.Functor.Foldable (Base, cata, para)
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.Maybe (fromJust)
import Data.Void (Void)
import Data.Word (Word8)
import PrettyPrint (indentSansFirstLine)
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), Parsec, Pos,
                        PosState (pstateSourcePos),
                        SourcePos (sourceColumn, sourceLine),
                        State (statePosState), between, choice,
                        errorBundlePretty, getParserState, many, manyTill,
                        optional, runParser, sepBy, some, unPos, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Pos (Pos)
import Text.Read (readMaybe)
import Text.Show.Deriving (deriveShow1)

type AnnotatedUPT = Cofree UnprocessedParsedTermF LocTag

instance Plated UnprocessedParsedTerm where
  plate f = \case
    ITEUP i t e -> ITEUP <$> f i <*> f t <*> f e
    LetUP l x   -> LetUP <$> traverse (sequenceA . second f) l <*> f x
    CaseUP x l  -> CaseUP <$> f x <*> traverse (sequenceA . second f) l
    ListUP l    -> ListUP <$> traverse f l
    PairUP a b  -> PairUP <$> f a <*> f b
    AppUP u x   -> AppUP <$> f u <*> f x
    LamUP s x   -> LamUP s <$> f x
    LeftUP x    -> LeftUP <$> f x
    RightUP x   -> RightUP <$> f x
    TraceUP x   -> TraceUP <$> f x
    HashUP x    -> HashUP <$> f x
    CheckUP c x -> CheckUP <$> f c <*> f x
    UnsizedRecursionUP x y z -> UnsizedRecursionUP <$> f x <*> f y <*> f z
    x           -> pure x

-- |TelomareParser :: * -> *
type TelomareParser = Parsec Void String

-- |Parse a variable.
parseVariable :: TelomareParser AnnotatedUPT
parseVariable = do
  s <- getParserState
  let line = unPos . sourceLine . pstateSourcePos . statePosState $ s
      column = unPos . sourceColumn . pstateSourcePos . statePosState $ s
  (\str -> Loc line column :< VarUPF str) <$> identifier

-- |Line comments start with "--".
lineComment :: TelomareParser ()
lineComment = L.skipLineComment "--"

-- |A block comment starts with "{-" and ends at "-}".
-- Nested block comments are also supported.
blockComment :: TelomareParser ()
blockComment = L.skipBlockCommentNested "{-" "-}"

-- |Space Consumer: Whitespace and comment parser that does not consume new-lines.
sc :: TelomareParser ()
sc = L.space
  (void $ some (char ' ' <|> char '\t'))
  lineComment
  blockComment

-- |Space Consumer: Whitespace and comment parser that does consume new-lines.
scn :: TelomareParser ()
scn = L.space space1 lineComment blockComment

-- |This is a wrapper for lexemes that picks up all trailing white space
-- using sc
lexeme :: TelomareParser a -> TelomareParser a
lexeme = L.lexeme sc

-- |A parser that matches given text using string internally and then similarly
-- picks up all trailing white space.
symbol :: String -> TelomareParser String
symbol = L.symbol sc

-- |This is to parse reserved words.
reserved :: String -> TelomareParser ()
reserved w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

-- |List of reserved words
rws :: [String]
rws = ["let", "in", "if", "then", "else", "case", "of", "import"]

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: TelomareParser String
identifier = lexeme . try $ p >>= check
  where
    p = (:) <$> letterChar <*> many (alphaNumChar <|> char '_' <|> char '.' <?> "variable")
    check x = if x `elem` rws
              then fail ("keyword " <> (show x <> " cannot be an identifier"))
              else pure x

-- |Parser for parenthesis.
parens :: TelomareParser a -> TelomareParser a
parens = between (symbol "(") (symbol ")")

-- |Parser for brackets.
brackets :: TelomareParser a -> TelomareParser a
brackets = between (symbol "[") (symbol "]")

-- |Parser for curly braces
curlies :: TelomareParser a -> TelomareParser a
curlies = between (symbol "{") (symbol "}")

-- |Comma sepparated TelomareParser that will be useful for lists
commaSep :: TelomareParser a -> TelomareParser [a]
commaSep p = p `sepBy` symbol ","

-- |Integer TelomareParser used by `parseNumber` and `parseChurch`
integer :: TelomareParser Integer
integer = toInteger <$> lexeme L.decimal

getLineColumn = do
  s <- getParserState
  let line = unPos . sourceLine . pstateSourcePos . statePosState $ s
      column = unPos . sourceColumn . pstateSourcePos . statePosState $ s
  pure $ Loc line column

-- |Parse string literal.
parseString :: TelomareParser AnnotatedUPT
parseString = do
  x <- getLineColumn
  (\str -> x :< StringUPF str) <$> (char '"' >> manyTill L.charLiteral (char '"' <* sc))

-- |Parse number (Integer).
parseNumber :: TelomareParser AnnotatedUPT
parseNumber = do
  x <- getLineColumn
  (\i -> x :< (IntUPF . fromInteger $ i)) <$> integer

-- |Parse a pair.
parsePair :: TelomareParser AnnotatedUPT
parsePair = parens $ do
  x <- getLineColumn
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ x :< PairUPF a b

-- |Parse unsized recursion triple
parseUnsizedRecursion :: TelomareParser AnnotatedUPT
parseUnsizedRecursion = curlies $ do
  x <- getLineColumn
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  _ <- symbol "," <* scn
  c <- parseLongExpr <* scn
  pure $ x :< UnsizedRecursionUPF a b c

-- |Parse a list.
parseList :: TelomareParser AnnotatedUPT
parseList = do
  x <- getLineColumn
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ x :< ListUPF exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: TelomareParser AnnotatedUPT
parseITE = do
  x <- getLineColumn
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  pure $ x :< ITEUPF cond thenExpr elseExpr

parseHash :: TelomareParser AnnotatedUPT
parseHash = do
  x <- getLineColumn
  symbol "#" <* scn
  upt <- parseSingleExpr
  pure $ x :< HashUPF upt

parseCase :: TelomareParser AnnotatedUPT
parseCase = do
  x <- getLineColumn
  reserved "case" <* scn
  iexpr <- parseLongExpr <* scn
  reserved "of" <* scn
  lpc <- some $ try parseSingleCase <* scn
  pure $ x :< CaseUPF iexpr lpc

parseSingleCase :: TelomareParser (Pattern, AnnotatedUPT)
parseSingleCase = do
  p <- parsePattern <* scn
  reserved "->" <* scn
  c <- parseLongExpr <* scn
  pure (p, c)

parsePattern :: TelomareParser Pattern
parsePattern = choice $ try <$> [ parsePatternIgnore
                                , parsePatternVar
                                , parsePatternString
                                , parsePatternInt
                                , parsePatternPair
                                ]

parsePatternPair :: TelomareParser Pattern
parsePatternPair = parens $ do
  p <- scn *> parsePattern <* scn
  _ <- symbol "," <* scn
  b <- parsePattern <* scn
  pure $ PatternPair p b

parsePatternInt :: TelomareParser Pattern
parsePatternInt = PatternInt . fromInteger <$> integer

parsePatternString :: TelomareParser Pattern
parsePatternString = PatternString <$> (char '"' >> manyTill L.charLiteral (char '"'))

parsePatternVar :: TelomareParser Pattern
parsePatternVar = PatternVar <$> identifier

parsePatternIgnore :: TelomareParser Pattern
parsePatternIgnore = symbol "_" >> pure PatternIgnore

-- |Parse a single expression.
parseSingleExpr :: TelomareParser AnnotatedUPT
parseSingleExpr = choice $ try <$> [ parseHash
                                   , parseString
                                   , parseNumber
                                   , parsePair
                                   , parseUnsizedRecursion
                                   , parseList
                                   , parseChurch
                                   , parseVariable
                                   , parens (scn *> parseLongExpr <* scn)
                                   ]

-- |Parse application of functions.
parseApplied :: TelomareParser AnnotatedUPT
parseApplied = do
  x <- getLineColumn
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) ->
      pure $ foldl (\a b -> x :< AppUPF a b) f args
    _ -> fail "expected expression"

-- |Parse lambda expression.
parseLambda :: TelomareParser AnnotatedUPT
parseLambda = do
  x <- getLineColumn
  symbol "\\" <* scn
  variables <- some identifier <* scn
  symbol "->" <* scn
  -- TODO make sure lambda names don't collide with bound names
  term1expr <- parseLongExpr <* scn
  pure $ foldr (\str upt -> x :< LamUPF str upt) term1expr variables

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> TelomareParser a -> TelomareParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  if pos == lvl then parser else fail "Expected same indentation."

-- |Parse let expression.
parseLet :: TelomareParser AnnotatedUPT
parseLet = do
  x <- getLineColumn
  reserved "let" <* scn
  lvl <- L.indentLevel
  bindingsList <- manyTill (parseSameLvl lvl parseAssignment) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  pure $ x :< LetUPF bindingsList expr

-- |Parse long expression.
parseLongExpr :: TelomareParser AnnotatedUPT
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseCase
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser AnnotatedUPT
parseChurch = do
  x <- getLineColumn
  (\upt -> x :< ChurchUPF upt) . fromInteger <$> (symbol "$" *> integer)

-- |Parse refinement check.
parseRefinementCheck :: TelomareParser (AnnotatedUPT -> AnnotatedUPT)
parseRefinementCheck = do
  x <- getLineColumn
  (\a b -> x :< CheckUPF a b) <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: TelomareParser (String, AnnotatedUPT)
parseAssignment = do
  var <- identifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  case annotation of
    Just annot -> pure (var, annot expr)
    _          -> pure (var, expr)

-- |Parse top level expressions.
parseTopLevel :: TelomareParser AnnotatedUPT
parseTopLevel = parseTopLevelWithExtraModuleBindings []

parseImport :: TelomareParser AnnotatedUPT
parseImport = do
  x <- getLineColumn
  reserved "import" <* scn
  var <- identifier <* scn
  pure $ x :< ImportUPF var

parseImportQualified :: TelomareParser AnnotatedUPT
parseImportQualified = do
  x <- getLineColumn
  reserved "import" <* scn
  var <- identifier <* scn
  reserved "qualified" <* scn
  qualifier <- identifier <* scn
  pure $ x :< ImportQualifiedUPF qualifier var

resolveImports :: [(String, [(String, AnnotatedUPT)])] -> AnnotatedUPT -> [(String, AnnotatedUPT)]
resolveImports modules = \case
  (_ :< (ImportUPF var)) ->
    case lookup var modules of
      Nothing -> error $ "Import error from " <> var
      Just x -> x
  (_ :< (ImportQualifiedUPF q v)) ->
    case lookup v modules of
      Nothing -> error $ "Import error from " <> v
      Just x -> (fmap . first) (\str -> q <> "." <> str) x
  _ -> error "Expected import statement"

-- resolveMain :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -- ^Modules: [(ModuleName, [Either Import (VariableName, BindedUPT)])]
--             -> String -- ^Module name with main
--             -> Either String AnnotatedUPT


-- |Parse top level expressions.
parseTopLevelWithExtraModuleBindings :: [(String, AnnotatedUPT)]
                                     -> TelomareParser AnnotatedUPT
parseTopLevelWithExtraModuleBindings lst = do
  x <- getLineColumn
  bindingList <- scn *> many parseAssignment <* eof
  pure $ x :< LetUPF (lst <> bindingList) (fromJust $ lookup "main" bindingList)


-- -- |Parse top level expressions.
-- parseTopLevelWithExtraModuleBindings :: [(String, AnnotatedUPT)]    -- ^Extra Module Bindings
--                                      -> TelomareParser AnnotatedUPT
-- parseTopLevelWithExtraModuleBindings mb = do
--   x <- getLineColumn
--   importList' <- scn *> many (try parseImportQualified <|> try parseImport) <* scn
--   let importList = undefined -- concat $ resolveImports mb <$> importList'
--   bindingList <- scn *> many parseAssignment <* eof
--   pure $ x :< LetUPF (importList <> bindingList) (fromJust $ lookup "main" bindingList)

parseDefinitions :: TelomareParser (AnnotatedUPT -> AnnotatedUPT)
parseDefinitions = do
  x <- getLineColumn
  bindingList <- scn *> many parseAssignment <* eof
  pure $ \y -> x :< LetUPF bindingList y

-- |Helper function to test parsers without a result.
runTelomareParser_ :: Show a => TelomareParser a -> String -> IO ()
runTelomareParser_ parser str = runTelomareParser parser str >>= print

-- |Helper function to debug parsers without a result.
runTelomareParserWDebug :: Show a => TelomareParser a -> String -> IO ()
runTelomareParserWDebug parser str = runTelomareParser (dbg "debug" parser) str >>= print

-- modulesAux :: [(String, [(String, AnnotatedUPT)])]
-- modulesAux = [("Prelude",[("id", DummyLoc :< LamUPF "x" (DummyLoc :< VarUPF "x")), ("id2", DummyLoc :< LamUPF "x2" (DummyLoc :< VarUPF "x2"))])]
-- parseImportOrAssignment

-- |Helper function to test Telomare parsers with any result.
runTelomareParser :: Monad m => TelomareParser a -> String -> m a
runTelomareParser parser str =
  case runParser parser "" str of
    Right x -> pure x
    Left e  -> error $ errorBundlePretty e

-- |Helper function to test if parser was successful.
parseSuccessful :: Monad m => TelomareParser a -> String -> m Bool
parseSuccessful parser str =
  case runParser parser "" str of
    Right _ -> pure True
    Left _  -> pure False

runParseLongExpr :: String -> Either String UnprocessedParsedTerm
runParseLongExpr str = bimap errorBundlePretty forget' $ runParser parseLongExpr "" str
  where
    forget' :: Cofree UnprocessedParsedTermF LocTag -> UnprocessedParsedTerm
    forget' = forget

parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePrelude str = let result = runParser (scn *> many parseAssignment <* eof) "" str
                    in first errorBundlePretty result

parseImportOrAssignment :: TelomareParser (Either AnnotatedUPT (String, AnnotatedUPT))
parseImportOrAssignment = do
  x <- getLineColumn
  maybeImport <- optional $ scn *> (try parseImportQualified <|> try parseImport) <* scn
  case maybeImport of
    Nothing -> do
      maybeAssignment <- optional $ scn *> try parseAssignment <* scn
      case maybeAssignment of
        Nothing -> fail "Expected either an import statement or an assignment"
        Just a -> pure $ Right a
    Just imp -> pure $ Left imp

input = unlines
  [ "import Prelude"
  , "foo = bar"
  , "baz = wee"
  , "import Foo"
  , "main = id"
  ]
aux = runTelomareParserWDebug (scn *> many parseImportOrAssignment <* eof) input

-- parseTopLevelWithExtraModuleBindings :: [(String, AnnotatedUPT)]
--                                      -> TelomareParser AnnotatedUPT

parseWithPrelude :: [(String, AnnotatedUPT)]   -- ^Prelude
                 -> String                     -- ^Raw string to be parsed
                 -> Either String AnnotatedUPT -- ^Error on Left
parseWithPrelude prelude str = first errorBundlePretty $ runParser (parseTopLevelWithExtraModuleBindings prelude) "" str

parseModule :: String -> Either String [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModule str = let result = runParser (scn *> many parseImportOrAssignment <* eof) "" str
                  in first errorBundlePretty result

-- |Parse either a single expression or top level definitions defaulting to the `main` definition.
--  This function was made for telomare-evaluare
parseOneExprOrTopLevelDefs :: [(String, AnnotatedUPT)] -> TelomareParser AnnotatedUPT
parseOneExprOrTopLevelDefs extraModuleBindings =
  choice $ try <$> [ parseTopLevelWithExtraModuleBindings extraModuleBindings
                   , parseLongExpr
                   ]
