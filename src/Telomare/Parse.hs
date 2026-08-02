{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parse where

import Control.Comonad.Cofree (Cofree (..), unwrap)
import qualified Control.Comonad.Trans.Cofree as C (CofreeF (..))
import Control.Lens.Plated (Plated (..))
import Control.Monad (join, void)
import Control.Monad.State (State)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Char (isUpper)
import Data.Fix (Fix (..))
import Data.Functor (($>))
import Data.Functor.Foldable (Base, cata, embed, para, project)
import Data.Functor.Foldable.TH (MakeBaseFunctor (makeBaseFunctor))
import Data.Maybe (fromJust)
import Data.Void (Void)
import Data.Word (Word8)
import GHC.Desugar (AnnotationWrapper (AnnotationWrapper))
import qualified System.IO.Strict as Strict
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Parse.Sugar (AssignmentEntry (..), buildMultiLambda,
                             expandAssignmentEntry)
import Telomare.PrettyPrint.Indent (indentSansFirstLine)
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), ParseErrorBundle,
                        Parsec, Pos,
                        SourcePos (sourceColumn, sourceLine, sourceName),
                        between, choice, errorBundlePretty, getOffset,
                        getSourcePos, many, manyTill, optional, runParser,
                        sepBy, some, unPos, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Pos (Pos)
import Text.Read (readMaybe)
import Text.Show.Deriving (deriveShow1)

-- |TelomareParser :: * -> *
type TelomareParser = Parsec Void String

-- |Parse a variable.
parseVariable :: TelomareParser AUPT
parseVariable = do
  (loc, str) <- withSourceSpan identifierRaw
  pure $ loc :< embedL (VarF str)

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
identifier = lexeme identifierRaw

identifierRaw :: TelomareParser String
identifierRaw = try $ p >>= check
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
integer = lexeme integerRaw

integerRaw :: TelomareParser Integer
integerRaw = toInteger <$> L.decimal

sourcePositionFromPos :: Int -> SourcePos -> SourcePosition
sourcePositionFromPos offset pos = SourcePosition
  { sourcePositionLine = unPos $ sourceLine pos
  , sourcePositionColumn = unPos $ sourceColumn pos
  , sourcePositionOffset = offset
  }

sourceLocFromPositions :: (Int, SourcePos) -> (Int, SourcePos) -> LocTag
sourceLocFromPositions (startOffset, start) (endOffset, end) = SourceLoc SourceSpan
  { sourceSpanFile = case sourceName start of
      ""   -> Nothing
      name -> Just name
  , sourceSpanStart = sourcePositionFromPos startOffset start
  , sourceSpanEnd = sourcePositionFromPos endOffset end
  }

withSourceSpan :: TelomareParser a -> TelomareParser (LocTag, a)
withSourceSpan parser = do
  startOffset <- getOffset
  start <- getSourcePos
  x <- parser
  endOffset <- getOffset
  end <- getSourcePos
  sc
  pure (sourceLocFromPositions (startOffset, start) (endOffset, end), x)

getSourceLoc :: TelomareParser LocTag
getSourceLoc = do
  offset <- getOffset
  pos <- getSourcePos
  pure $ sourceLocFromPositions (offset, pos) (offset, pos)

-- |Parse string literal.
parseString :: TelomareParser AUPT
parseString = do
  (x, str) <- withSourceSpan (char '"' >> manyTill L.charLiteral (char '"'))
  pure $ x :< StringUPF str

-- |Parse number (Integer).
parseNumber :: TelomareParser AUPT
parseNumber = do
  (x, i) <- withSourceSpan integerRaw
  pure $ x :< (IntUPF . fromInteger $ i)

-- |Parse a pair.
parsePair :: TelomareParser AUPT
parsePair = parens $ do
  x <- getSourceLoc
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  pure $ x :< embedB (PairSF a b)

-- |Parse unsized recursion triple
parseUnsizedRecursion :: TelomareParser AUPT
parseUnsizedRecursion = curlies $ do
  x <- getSourceLoc
  a <- scn *> parseLongExpr <* scn
  _ <- symbol "," <* scn
  b <- parseLongExpr <* scn
  _ <- symbol "," <* scn
  c <- parseLongExpr <* scn
  pure $ x :< embedH (RecursionF a b c)

-- |Parse a list.
parseList :: TelomareParser AUPT
parseList = do
  x <- getSourceLoc
  exprs <- brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ x :< ListUPF exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: TelomareParser AUPT
parseITE = do
  x <- getSourceLoc
  reserved "if" <* scn
  cond <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "then" <* scn
  thenExpr <- (parseLongExpr <|> parseSingleExpr) <* scn
  reserved "else" <* scn
  elseExpr <- parseLongExpr <* scn
  pure $ x :< embedH (ITEF cond thenExpr elseExpr)

parseHash :: TelomareParser AUPT
parseHash = do
  x <- getSourceLoc
  symbol "#" <* scn
  upt <- parseSingleExpr
  pure $ x :< embedH (HashF upt)

parseListAssignment :: TelomareParser AssignmentEntry
parseListAssignment = do
  x <- getSourceLoc
  names <- (brackets (commaSep (scn *> locatedNameParser <* scn)) <* scn)
           <?> "list assignment names"
  (scn *> symbol "=") <?> "list assignment ="
  expr <- (scn *> parseLongExpr <* scn) <?> "list assignment body"
  pure $ ListAssignment x names expr

locatedIdentifier :: TelomareParser (LocTag, String)
locatedIdentifier = lexeme $ withSourceSpan identifierRaw

locatedNameParser :: TelomareParser LocatedName
locatedNameParser = uncurry locatedName <$> locatedIdentifier

parseCase :: TelomareParser AUPT
parseCase = do
  x <- getSourceLoc
  reserved "case" <* scn
  iexpr <- parseLongExpr <* scn
  reserved "of" <* scn
  lpc <- some $ try parseSingleCase <* scn
  pure $ x :< CaseUPF iexpr lpc

parseSingleCase :: TelomareParser (PatternA, AUPT)
parseSingleCase = do
  p <- parsePattern <* scn
  reserved "->" <* scn
  c <- parseLongExpr <* scn
  pure (p, c)

parsePattern :: TelomareParser PatternA
parsePattern = choice $ try <$> [ parsePatternIgnore
                                 , parsePatternVar
                                 , parsePatternAnnotated
                                 , parsePatternString
                                 , parsePatternInt
                                 , parsePatternPair
                                 ]

parseLocatedPattern :: TelomareParser (LocTag, PatternA)
parseLocatedPattern = choice $ try <$> [ parseLocatedPatternVar
                                       , parseLocatedPatternOther
                                       ]

parseLocatedPatternVar :: TelomareParser (LocTag, PatternA)
parseLocatedPatternVar = do
  (loc, name) <- locatedIdentifier <* scn
  pure (loc, embed $ PatternVarF name)

parseLocatedPatternOther :: TelomareParser (LocTag, PatternA)
parseLocatedPatternOther = do
  loc <- getSourceLoc
  pattern' <- choice $ try <$> [ parsePatternIgnore
                               , parsePatternAnnotated
                               , parsePatternString
                               , parsePatternInt
                               , parsePatternPair
                               ]
  pure (loc, pattern')

parsePatternPair :: TelomareParser PatternA
parsePatternPair = parens $ do
  p <- scn *> parsePattern <* scn
  _ <- symbol "," <* scn
  b <- parsePattern <* scn
  pure . embed $ PatternPairF p b

parsePatternInt :: TelomareParser PatternA
parsePatternInt = embed . PatternIntF . fromInteger <$> integer

parsePatternString :: TelomareParser PatternA
parsePatternString =  embed . PatternStringF <$> (char '"' >> manyTill L.charLiteral (char '"'))

parsePatternVar :: TelomareParser PatternA
parsePatternVar =  embed . PatternVarF <$> (identifier <* scn)
-- Pattern annotations are only accepted in parenthesised form
-- (parsePatternAnnotated). Allowing a bare @v : T@ here would shadow
-- the parenthesised path because parsePatternVar runs first in
-- parsePattern's @choice@.


parsePatternIgnore :: TelomareParser PatternA
parsePatternIgnore = symbol "_" >> pure (embed PatternIgnoreF)

-- |Parse a parenthesised pattern with a type/refinement annotation,
-- e.g. @(aa : Nat)@. The stored typeExpr is the raw check function;
-- 'buildMultiLambda' applies it to the bound value and uses the result as
-- the case scrutinee, forcing runtime validation before destructuring.
parsePatternAnnotated :: TelomareParser PatternA
parsePatternAnnotated = parens body <?> "annotated pattern"
  where
    body = do
      p <- (scn *> parsePattern <* scn) <?> "pattern before ':'"
      symbol ":" <* scn
      typeExpr <- (parseLongExpr <* scn) <?> "type expression after ':'"
      pure . embed $ PatternAnnotatedF p (AnnotatedUPT typeExpr)

-- |Parse a single expression.
parseSingleExpr :: TelomareParser AUPT
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
parseApplied :: TelomareParser AUPT
parseApplied = do
  x <- getSourceLoc
  fargs <- L.lineFold scn $ \sc' ->
    parseSingleExpr `sepBy` try sc'
  case fargs of
    (f:args) ->
      pure $ foldl (\a b -> x :< embedL (AppF a b)) f args
    _ -> fail "expected expression"

-- |Parse lambda expression.
parseLambda :: TelomareParser AUPT
parseLambda = do
  x <- getSourceLoc
  symbol "\\" <* scn
  variables <- some parseLocatedPattern <* scn
  symbol "->" <* scn
  term1expr <- parseLongExpr <* scn
  pure $ buildMultiLambda x variables term1expr

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> TelomareParser a -> TelomareParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  if pos == lvl then parser else fail "Expected same indentation."

-- |Parse let expression. Accepts both plain @name = value@ assignments
-- and list assignments @[n1, n2, ...] = value@. UDT declarations are
-- a specialized list-assignment convention.
parseLet :: TelomareParser AUPT
parseLet = do
  x <- getSourceLoc
  reserved "let" <* scn
  lvl <- L.indentLevel
  entries <- manyTill (parseSameLvl lvl parseAssignmentEntry) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  let bindingsList = entries >>= expandAssignmentEntry
  pure $ x :< LetUPF bindingsList expr

-- |Parse long expression.
parseLongExpr :: TelomareParser AUPT
parseLongExpr = choice $ try <$> [ parseLet
                                 , parseITE
                                 , parseLambda
                                 , parseApplied
                                 , parseCase
                                 , parseSingleExpr
                                 ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser AUPT
parseChurch = do
  (x, upt) <- withSourceSpan (char '$' *> integerRaw)
  pure . (x :<) . embedH . ChurchF $ fromInteger upt

-- |Parse refinement check.
parseRefinementCheck :: TelomareParser (AUPT -> AUPT)
parseRefinementCheck = do
  x <- getSourceLoc
  (\a b -> x :< embedH (CheckF a b)) <$> (symbol ":" *> parseLongExpr)

-- |Parse assignment add adding binding to ParserState.
parseAssignment :: TelomareParser (String, AUPT)
parseAssignment = do
  (var, expr) <- parseLocatedAssignment
  pure (locatedNameText var, expr)

parseLocatedAssignment :: TelomareParser (LocatedName, AUPT)
parseLocatedAssignment = do
  (loc, var) <- locatedIdentifier <* scn
  annotation <- optional . try $ parseRefinementCheck
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  case annotation of
    Just annot -> pure (locatedName loc var, annot expr)
    _          -> pure (locatedName loc var, expr)

-- |Parse top level expressions.
parseTopLevel :: TelomareParser AUPT
parseTopLevel = parseTopLevelWithExtraModuleBindings []

parseImport :: TelomareParser AUPT
parseImport = do
  x <- getSourceLoc
  reserved "import" <* scn
  var <- identifier <* scn
  pure $ x :< ImportUPF var

parseImportQualified :: TelomareParser AUPT
parseImportQualified = do
  x <- getSourceLoc
  reserved "import" <* scn
  reserved "qualified" <* scn
  m <- identifier <* scn
  reserved "as" <* scn
  qualifier <- identifier <* scn
  pure $ x :< ImportQualifiedUPF qualifier m

-- |A single top-level entry is either a name=value assignment or a list
-- assignment `[n1, n2, …] = expr`. UDTs are recognized as a specialized
-- uppercase-lambda list assignment during expansion.
parseAssignmentEntry :: TelomareParser AssignmentEntry
parseAssignmentEntry =
  uncurry SingleAssignment <$> parseLocatedAssignment
    <|> parseListAssignment

-- |Parse assignments, expanding list assignments into their per-slot bindings.
parseAssignmentEntries :: TelomareParser [(String, AUPT)]
parseAssignmentEntries = do
  fmap (first locatedNameText) <$> parseLocatedAssignmentEntries

parseLocatedAssignmentEntries :: TelomareParser [(LocatedName, AUPT)]
parseLocatedAssignmentEntries = do
  entries <- scn *> many parseAssignmentEntry <* eof
  pure (expandAssignmentEntry =<< entries)

-- |Parse top level expressions. Fails with a megaparsec error if the
-- module has no @main@ definition, instead of crashing with 'fromJust'.
parseTopLevelWithExtraModuleBindings :: [(String, AUPT)]
                                     -> TelomareParser AUPT
parseTopLevelWithExtraModuleBindings lst = do
  x <- getSourceLoc
  bindingList <- parseLocatedAssignmentEntries
  case lookup "main" $ first locatedNameText <$> bindingList of
    Just m  -> pure $ x :< LetUPF ((first (locatedName UnknownLoc) <$> lst) <> bindingList) m
    Nothing -> fail "missing 'main' definition"

-- |Helper function to test parsers without a result.
runTelomareParser_ :: Show a => TelomareParser a -> String -> IO ()
runTelomareParser_ parser str = runTelomareParser parser str >>= print

-- |Helper function to debug parsers without a result.
runTelomareParserWDebug :: Show a => TelomareParser a -> String -> IO ()
runTelomareParserWDebug parser str = runTelomareParser (dbg "debug" parser) str >>= print

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
runParseLongExpr str = bimap errorBundlePretty convert $ runParser parseLongExpr "" str
  where
    convert = UnprocessedParsedTerm . cata f where
      f :: C.CofreeF (UnprocessedParsedTermF PatternA) LocTag (Fix (UnprocessedParsedTermF Pattern)) -> Fix (UnprocessedParsedTermF Pattern)
      f (_ C.:< f') = embed $ case f' of
        UnprocessedParsedTermB x -> UnprocessedParsedTermB x
        UnprocessedParsedTermH x -> UnprocessedParsedTermH x
        LetUPF bindings x        -> LetUPF bindings x
        ListUPF x                -> ListUPF x
        IntUPF n                 -> IntUPF n
        StringUPF s              -> StringUPF s
        UDTUPF names x           -> UDTUPF names x
        CaseUPF x matches        -> CaseUPF x $ fmap cp matches
        ImportQualifiedUPF a b   -> ImportQualifiedUPF a b
        ImportUPF s              -> ImportUPF s
      cp (p, b) = (cata (embed . pf) p, b)
      pf = \case
        PatternVarF s ->PatternVarF s
        PatternAnnotatedF x (AnnotatedUPT t) -> PatternAnnotatedF x (UnprocessedParsedTerm $ cata f t)
        PatternIntF n -> PatternIntF n
        PatternStringF s -> PatternStringF s
        PatternIgnoreF -> PatternIgnoreF
        PatternPairF a b -> PatternPairF a b

parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePrelude = parsePreludeNamed ""

-- |`parsePrelude`, recording the source name in every location it produces so
-- diagnostics can say which file a term came from.
parsePreludeNamed :: String -> String -> Either String [(String, AnnotatedUPT)]
parsePreludeNamed name str = let result = runParser parseAssignmentEntries name str
                             in bimap errorBundlePretty (fmap (second AnnotatedUPT)) result

-- |One parser step inside a module: returns a list because list assignments
-- expand into multiple (name, value) bindings.
-- TODO change this type to something more reasonable
parseImportOrAssignment :: TelomareParser [Either AUPT (String, AUPT)]
parseImportOrAssignment = do
  maybeImport <- optional $ scn *> (try parseImportQualified <|> try parseImport) <* scn
  case maybeImport of
    Nothing -> do
      maybeEntry <- optional $ scn *> try parseAssignmentEntry <* scn
      case maybeEntry of
        Nothing    -> fail "Expected either an import statement or an assignment"
        Just entry -> pure (Right . first locatedNameText <$> expandAssignmentEntry entry)
    Just imp -> pure [Left imp]

parseWithPrelude :: [(String, AnnotatedUPT)]   -- ^Prelude
                 -> String                     -- ^Raw string to be parsed
                 -> Either String AnnotatedUPT -- ^Error on Left
parseWithPrelude prelude str = bimap errorBundlePretty AnnotatedUPT $ runParser (parseTopLevelWithExtraModuleBindings prelude') "" str where
  prelude' = fmap (second unAnnotatedUPT) prelude

parseModule :: String -> Either String [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModule = parseModuleNamed ""

-- |`parseModule`, recording the source name in every location it produces so
-- diagnostics can say which file a term came from.
parseModuleNamed :: String -> String -> Either String [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModuleNamed name str = first errorBundlePretty $ parseModuleDetailedNamed name str

parseModuleDetailed :: String -> Either (ParseErrorBundle String Void) [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModuleDetailed = parseModuleDetailedNamed ""

parseModuleDetailedNamed :: String -> String -> Either (ParseErrorBundle String Void) [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModuleDetailedNamed name = wrapUp . runParser (concat <$> (scn *> many parseImportOrAssignment <* eof)) name where
  wrapUp = second (fmap (bimap AnnotatedUPT (second AnnotatedUPT)))

-- |Parse either a single expression or top level definitions defaulting to the `main` definition.
--  This function was made for telomare-evaluare
parseOneExprOrTopLevelDefs :: [(String, AUPT)] -> TelomareParser AUPT
parseOneExprOrTopLevelDefs extraModuleBindings =
  choice $ try <$> [ parseTopLevelWithExtraModuleBindings extraModuleBindings
                   , parseLongExpr
                   ]
