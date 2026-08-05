{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parse where

import Control.Comonad.Cofree (Cofree (..))
import Control.Monad (void)
import Data.Bifunctor (first)
import Data.Functor.Foldable (embed)
import Data.Void (Void)
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), ParseErrorBundle,
                        Parsec, Pos,
                        SourcePos (sourceColumn, sourceLine, sourceName),
                        between, choice, errorBundlePretty, getOffset,
                        getSourcePos, many, manyTill, optional, runParser,
                        sepBy, sepBy1, some, unPos, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)

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
reserved w = (lexeme . try) (string w *> notFollowedBy identifierContinue)

-- |List of reserved words
rws :: [String]
rws = ["let", "in", "if", "then", "else", "case", "of", "import", "qualified", "as"]

identifierContinue :: TelomareParser Char
identifierContinue = alphaNumChar <|> char '_' <|> char '.'

-- |Variable identifiers can consist of alphanumeric characters, underscore,
-- and must start with an English alphabet letter
identifier :: TelomareParser String
identifier = lexeme identifierRaw

identifierRaw :: TelomareParser String
identifierRaw = try $ p >>= check
  where
    p = (:) <$> letterChar <*> many (identifierContinue <?> "variable")
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

commaSep1 :: TelomareParser a -> TelomareParser [a]
commaSep1 p = p `sepBy1` symbol ","

-- |Integer TelomareParser used by `parseNumber` and `parseChurch`
integer :: TelomareParser Integer
integer = lexeme integerRaw

integerRaw :: TelomareParser Integer
integerRaw = L.decimal

naturalIntRaw :: TelomareParser Int
naturalIntRaw = do
  value <- integerRaw
  if value <= toInteger (maxBound :: Int)
    then pure $ fromInteger value
    else fail "natural literal exceeds the supported range"

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
withSourceSpan parser = captureSourceSpan parser <* sc

captureSourceSpan :: TelomareParser a -> TelomareParser (LocTag, a)
captureSourceSpan parser = do
  startOffset <- getOffset
  start <- getSourcePos
  x <- parser
  endOffset <- getOffset
  end <- getSourcePos
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
  (x, i) <- withSourceSpan naturalIntRaw
  pure $ x :< IntUPF i

-- |Parse a pair.
parsePair :: TelomareParser AUPT
parsePair = do
  (x, (a, b)) <- captureSourceSpan . parens $ do
    a <- scn *> parseLongExpr <* scn
    _ <- symbol "," <* scn
    b <- parseLongExpr <* scn
    pure (a, b)
  pure $ x :< embedB (PairSF a b)

-- |Parse unsized recursion triple
parseUnsizedRecursion :: TelomareParser AUPT
parseUnsizedRecursion = do
  (x, (a, b, c)) <- captureSourceSpan . curlies $ do
    a <- scn *> parseLongExpr <* scn
    _ <- symbol "," <* scn
    b <- parseLongExpr <* scn
    _ <- symbol "," <* scn
    c <- parseLongExpr <* scn
    pure (a, b, c)
  pure $ x :< embedH (RecursionF a b c)

-- |Parse a list.
parseList :: TelomareParser AUPT
parseList = do
  (x, exprs) <- captureSourceSpan $ brackets (commaSep (scn *> parseLongExpr <*scn))
  pure $ x :< ListUPF exprs

-- TODO: make error more descriptive
-- |Parse ITE (which stands for "if then else").
parseITE :: TelomareParser AUPT
parseITE = do
  (x, (cond, thenExpr, elseExpr)) <- captureSourceSpan $ do
    reserved "if" <* scn
    cond <- parseLongExpr <* scn
    reserved "then" <* scn
    thenExpr <- parseLongExpr <* scn
    reserved "else" <* scn
    elseExpr <- parseLongExpr <* scn
    pure (cond, thenExpr, elseExpr)
  pure $ x :< embedH (ITEF cond thenExpr elseExpr)

parseHash :: TelomareParser AUPT
parseHash = do
  (x, upt) <- captureSourceSpan $ symbol "#" <* scn *> parseSingleExpr
  pure $ x :< embedH (HashF upt)

parseListDefinition :: TelomareParser (DefinitionF AUPT)
parseListDefinition = do
  x <- getSourceLoc
  names <- (brackets (commaSep1 (scn *> locatedNameParser <* scn)) <* scn)
           <?> "list assignment names"
  (scn *> symbol "=") <?> "list assignment ="
  expr <- (scn *> parseLongExpr <* scn) <?> "list assignment body"
  pure $ ListDefF x names expr

locatedIdentifier :: TelomareParser (LocTag, String)
locatedIdentifier = lexeme $ withSourceSpan identifierRaw

locatedNameParser :: TelomareParser LocatedName
locatedNameParser = uncurry locatedName <$> locatedIdentifier

parseCase :: TelomareParser AUPT
parseCase = do
  (x, (iexpr, lpc)) <- captureSourceSpan $ do
    reserved "case" <* scn
    iexpr <- parseLongExpr <* scn
    reserved "of" <* scn
    lpc <- some $ try parseSingleCase <* scn
    pure (iexpr, lpc)
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
  pure (loc, embed . PatternVarF $ locatedName loc name)

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
parsePatternInt = embed . PatternIntF <$> lexeme naturalIntRaw

parsePatternString :: TelomareParser PatternA
parsePatternString =  embed . PatternStringF <$> (char '"' >> manyTill L.charLiteral (char '"'))

parsePatternVar :: TelomareParser PatternA
parsePatternVar = do
  (loc, name) <- locatedIdentifier <* scn
  pure . embed . PatternVarF $ locatedName loc name
-- Pattern annotations are only accepted in parenthesised form
-- (parsePatternAnnotated). Allowing a bare @v : T@ here would shadow
-- the parenthesised path because parsePatternVar runs first in
-- parsePattern's @choice@.


parsePatternIgnore :: TelomareParser PatternA
parsePatternIgnore = symbol "_" >> pure (embed PatternIgnoreF)

-- |Parse a parenthesised pattern with a type/refinement annotation,
-- e.g. @(aa : Nat)@. The stored typeExpr is the raw check function;
-- 'Telomare.Sugar.buildMultiLambda' applies it to the bound value and uses
-- the result as the case scrutinee, forcing runtime validation before
-- destructuring.
parsePatternAnnotated :: TelomareParser PatternA
parsePatternAnnotated = parens body <?> "annotated pattern"
  where
    body = do
      p <- (scn *> parsePattern <* scn) <?> "pattern before ':'"
      symbol ":" <* scn
      typeExpr <- (parseLongExpr <* scn) <?> "type expression after ':'"
      pure . embed $ PatternAnnotatedF p (AnnotatedUPT typeExpr)

-- |Parse an atomic expression.
parseAtom :: TelomareParser AUPT
parseAtom = choice $ try <$> [ parseHash
                             , parseString
                             , parseNumber
                             , parsePair
                             , parseUnsizedRecursion
                             , parseList
                             , parseChurch
                             , parseVariable
                             , parens (scn *> parseLongExpr <* scn)
                             ]

-- |Compatibility name for callers parsing an expression atom.
parseSingleExpr :: TelomareParser AUPT
parseSingleExpr = parseAtom

-- |Parse application of functions.
parseApplied :: TelomareParser AUPT
parseApplied = do
  (x, fargs) <- captureSourceSpan . L.lineFold scn
    $ \sc' -> parseAtom `sepBy1` try sc'
  case fargs of
    f:args -> pure $ foldl (\a b -> x :< embedL (AppF a b)) f args
    []     -> fail "expected expression"

-- |Parse an atom or a whitespace-separated application. The atom fallback
-- keeps a following, less-indented grammar delimiter from turning a complete
-- atom into a failed multiline application.
parseApplication :: TelomareParser AUPT
parseApplication = try parseApplied <|> parseAtom

-- |Parse lambda expression. Emits the raw multi-pattern form;
-- 'Telomare.Sugar.buildMultiLambda' turns it into nested plain lambdas
-- with case destructuring.
parseLambda :: TelomareParser AUPT
parseLambda = do
  (x, (variables, term1expr)) <- captureSourceSpan $ do
    symbol "\\" <* scn
    variables <- some parseLocatedPattern <* scn
    symbol "->" <* scn
    term1expr <- parseLongExpr <* scn
    pure (variables, term1expr)
  pure $ x :< LamPatUPF variables term1expr

-- |Parser that fails if indent level is not `pos`.
parseSameLvl :: Pos -> TelomareParser a -> TelomareParser a
parseSameLvl pos parser = do
  lvl <- L.indentLevel
  if pos == lvl then parser else fail "Expected same indentation."

-- |Parse let expression. Accepts both plain @name = value@ assignments
-- and list assignments @[n1, n2, ...] = value@. Entries are kept raw;
-- 'Telomare.Sugar' expands list assignments and UDT declarations into
-- their per-slot bindings.
parseLet :: TelomareParser AUPT
parseLet = do
  (x, (entries, expr)) <- captureSourceSpan $ do
    reserved "let" <* scn
    lvl <- L.indentLevel
    entries <- manyTill (parseSameLvl lvl parseDefinition) (reserved "in") <* scn
    expr <- parseLongExpr <* scn
    pure (entries, expr)
  pure $ x :< LetSugarUPF entries expr

-- |Parse long expression.
parseLongExpr :: TelomareParser AUPT
parseLongExpr = choice [ parseLet
                       , parseITE
                       , parseLambda
                       , parseCase
                       , parseApplication
                       ]

-- |Parse church numerals (church numerals are a "$" appended to an integer, without any whitespace separation).
parseChurch :: TelomareParser AUPT
parseChurch = do
  (x, upt) <- withSourceSpan (char '$' *> naturalIntRaw)
  pure . (x :<) . embedH $ ChurchF upt

-- |Parse a refinement annotation @: T@, keeping the type expression raw.
-- The 'LocTag' is captured at the @:@; 'Telomare.Sugar' folds the
-- annotation into a 'CheckF' node carrying it.
parseRefinementAnnotation :: TelomareParser (LocTag, AUPT)
parseRefinementAnnotation = do
  x <- getSourceLoc
  typeExpr <- symbol ":" *> parseLongExpr
  pure (x, typeExpr)

-- |Parse a single @name (: check)? = value@ definition, kept raw.
parseSingleDefinition :: TelomareParser (DefinitionF AUPT)
parseSingleDefinition = do
  (loc, var) <- locatedIdentifier <* scn
  annotation <- optional . try $ parseRefinementAnnotation
  scn *> symbol "=" <?> "assignment ="
  expr <- scn *> parseLongExpr <* scn
  pure $ SingleDefF (locatedName loc var) annotation expr

parseImport :: TelomareParser AUPT
parseImport = do
  importDecl <- parseImportDecl
  case parsedImportQualifier importDecl of
    Nothing -> pure $ parsedImportLoc importDecl :< ImportUPF
      (locatedNameText $ parsedImportModule importDecl)
    Just _ -> fail "expected an unqualified import"

parseImportQualified :: TelomareParser AUPT
parseImportQualified = do
  importDecl <- parseImportDecl
  case parsedImportQualifier importDecl of
    Nothing -> fail "expected a qualified import"
    Just qualifier -> pure $ parsedImportLoc importDecl :< ImportQualifiedUPF
      (locatedNameText qualifier)
      (locatedNameText $ parsedImportModule importDecl)

parseImportDecl :: TelomareParser ImportDecl
parseImportDecl = do
  (loc, (moduleName, qualifier)) <- captureSourceSpan $ do
    reserved "import" <* scn
    qualified <- optional . try $ reserved "qualified" <* scn
    moduleName <- locatedNameParser <* scn
    qualifier <- case qualified of
      Nothing -> pure Nothing
      Just () -> do
        reserved "as" <* scn
        Just <$> locatedNameParser
    pure (moduleName, qualifier)
  pure $ ImportDecl loc moduleName qualifier

-- |A single definition is either a name=value assignment or a list
-- assignment `[n1, n2, …] = expr` (UDTs are a specialized list-assignment
-- convention that 'Telomare.Sugar' recognizes during expansion).
parseDefinition :: TelomareParser (DefinitionF AUPT)
parseDefinition = parseSingleDefinition <|> parseListDefinition

-- |Parse a whole input of definitions, kept raw.
parseDefinitions :: TelomareParser [DefinitionF AUPT]
parseDefinitions = scn *> many parseDefinition <* scn <* eof

-- |Parse one complete expression, rejecting any trailing input.
parseExpression :: TelomareParser AUPT
parseExpression = scn *> parseLongExpr <* scn <* eof

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

-- |One item inside a module: an import declaration or a raw definition.
parseModuleItem :: TelomareParser (ModuleItem AUPT)
parseModuleItem = scn *>
  (ModuleImportItem <$> try parseImportDecl
    <|> ModuleDefinitionItem <$> parseDefinition)
  <* scn

parseModuleItems :: TelomareParser [ModuleItem AUPT]
parseModuleItems = scn *> many parseModuleItem <* eof

-- |Parse a module into raw items, keeping the megaparsec error bundle so
-- callers (the LSP server) can compute diagnostic ranges. The first
-- argument is the source name recorded in every location produced.
runParseModuleDetailed :: String -> String
                       -> Either (ParseErrorBundle String Void) (Parsed [ModuleItem AUPT])
runParseModuleDetailed name = fmap Parsed . runParser parseModuleItems name

-- |'runParseModuleDetailed' with the error pretty-printed.
runParseModule :: String -> String -> Either String (Parsed [ModuleItem AUPT])
runParseModule name = first errorBundlePretty . runParseModuleDetailed name

-- |Parse an input that is only definitions (e.g. a prelude file), kept
-- raw. The first argument is the source name recorded in every location
-- produced.
runParseDefinitions :: String -> String -> Either String (Parsed [DefinitionF AUPT])
runParseDefinitions name = first errorBundlePretty . fmap Parsed . runParser parseDefinitions name

-- |Parse one complete expression, recording the supplied source name.
runParseExpression :: String -> String -> Either String (Parsed AUPT)
runParseExpression name = first errorBundlePretty . fmap Parsed . runParser parseExpression name

-- |Parse either a whole block of top level definitions or a single
-- expression. Made for telomare-evaluare and the REPL's @:l@; the caller
-- decides what to do with each shape (typically 'Telomare.Sugar.wrapMain'
-- for definitions).
parseOneExprOrDefinitions :: TelomareParser (Either [DefinitionF AUPT] AUPT)
parseOneExprOrDefinitions =
  (Left <$> try parseDefinitions) <|> (Right <$> parseExpression)
