{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

import Control.Comonad.Cofree (Cofree (..), unwrap)
import Control.Lens.Plated (Plated (..))
import Control.Monad (join, void)
import Control.Monad.State (State)
import Data.Bifunctor (Bifunctor (first, second), bimap)
import Data.Char (isUpper)
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

data AssignmentEntry
  = SingleAssignment String AnnotatedUPT
  | ListAssignment LocTag [String] AnnotatedUPT

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

parseListAssignment :: TelomareParser AssignmentEntry
parseListAssignment = do
  x <- getLineColumn
  names :: [String] <- (brackets (commaSep (scn *> identifier <* scn)) <* scn)
                       <?> "list assignment names"
  (scn *> symbol "=") <?> "list assignment ="
  expr <- (scn *> parseLongExpr <* scn) <?> "list assignment body"
  pure $ ListAssignment x names expr

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
                                , parsePatternAnnotated
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
parsePatternVar = PatternVar <$> (identifier <* scn)
-- Pattern annotations are only accepted in parenthesised form
-- (parsePatternAnnotated). Allowing a bare @v : T@ here would shadow
-- the parenthesised path because parsePatternVar runs first in
-- parsePattern's @choice@.


parsePatternIgnore :: TelomareParser Pattern
parsePatternIgnore = symbol "_" >> pure PatternIgnore

-- |Parse a parenthesised pattern with a type/refinement annotation,
-- e.g. @(aa : Nat)@. The stored typeExpr is the raw check function;
-- 'buildMultiLambda' applies it to the bound value and uses the result as
-- the case scrutinee, forcing runtime validation before destructuring.
parsePatternAnnotated :: TelomareParser Pattern
parsePatternAnnotated = parens body <?> "annotated pattern"
  where
    body = do
      p <- (scn *> parsePattern <* scn) <?> "pattern before ':'"
      symbol ":" <* scn
      typeExpr <- (parseLongExpr <* scn) <?> "type expression after ':'"
      pure $ PatternAnnotated p (forget typeExpr)

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

-- |Generate a fresh-looking variable name from a pattern's shape, used
-- as the name of the lambda parameter that 'buildMultiLambda' introduces
-- before destructuring.
genPatternVarName :: Pattern -> String
genPatternVarName = ("generatedVar" <>)
                  . filter (\x -> x /= '\"'
                               && x /= ' '
                               && x /= '('
                               && x /= ')'
                               && x /= '['
                               && x /= ']')
                  . show

-- |Pick the lambda-bound variable name for a pattern: use the user's name
-- for a 'PatternVar', otherwise generate one.
lambdaVarName :: Pattern -> String
lambdaVarName = \case
  PatternVar str -> str
  p              -> genPatternVarName p

-- |Build a multi-argument lambda whose destructuring all happens INSIDE
-- the innermost lambda body. For @\\p1 p2 p3 -> body@ this emits
--
-- > \\v1 -> \\v2 -> \\v3 -> applyDestructure p3 v3
-- >                                 (applyDestructure p2 v2
-- >                                   (applyDestructure p1 v1 body))
--
-- where @applyDestructure p v body@ is @body@ when @p@ is a 'PatternVar'
-- (no destructure needed) and a @case v of p -> body@ otherwise.
--
-- This avoids putting a function-valued lambda inside a case body, which
-- would cause the case-rewrite to type-mismatch against the (Pair-typed)
-- abort fallback.
buildMultiLambda :: LocTag -> [Pattern] -> AnnotatedUPT -> AnnotatedUPT
buildMultiLambda lt patterns body =
  let varNames = lambdaVarName <$> patterns
      destructured = foldr applyDestructure body (zip patterns varNames)
      lamWrapped = foldr (\v inner -> lt :< LamUPF v inner) destructured varNames
  in lamWrapped
  where
    applyDestructure :: (Pattern, String) -> AnnotatedUPT -> AnnotatedUPT
    applyDestructure (p, varName) inner =
      let bound = lt :< VarUPF varName
          abort = lt :< AppUPF
                    (lt :< VarUPF "abort")
                    (lt :< StringUPF "buildMultiLambda: pattern not reached")
      in case p of
           PatternVar _ -> inner
           PatternAnnotated innerPat typeExpr ->
             -- Use the validator result as the case scrutinee instead of
             -- CheckUPF: hash-based UDT validators are runtime values that
             -- the static refinement analyzer cannot symbolically evaluate.
             let tyApplied = lt :< AppUPF (tag lt typeExpr) bound
             in lt :< CaseUPF tyApplied [(innerPat, inner)]
           _ ->
             lt :< CaseUPF bound
               [ (p, inner)
               , (PatternIgnore, abort)
               ]

-- |Build a single-argument lambda with optional destructuring.
-- Kept as a thin wrapper around 'buildMultiLambda' so existing callers
-- that work pattern-at-a-time continue to function.
makeLambda :: LocTag -> Pattern -> AnnotatedUPT -> AnnotatedUPT
makeLambda lt p = buildMultiLambda lt [p]

-- |Parse lambda expression.
parseLambda :: TelomareParser AnnotatedUPT
parseLambda = do
  x <- getLineColumn
  symbol "\\" <* scn
  variables <- some parsePattern <* scn
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
parseLet :: TelomareParser AnnotatedUPT
parseLet = do
  x <- getLineColumn
  reserved "let" <* scn
  lvl <- L.indentLevel
  entries <- manyTill (parseSameLvl lvl parseAssignmentEntry) (reserved "in") <* scn
  expr <- parseLongExpr <* scn
  let bindingsList = entries >>= expandAssignmentEntry
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
  (uncurry SingleAssignment <$> parseAssignment)
    <|> parseListAssignment

-- |Parse assignments, expanding list assignments into their per-slot bindings.
parseAssignmentEntries :: TelomareParser [(String, AnnotatedUPT)]
parseAssignmentEntries = do
  entries <- scn *> many parseAssignmentEntry <* eof
  pure (expandAssignmentEntry =<< entries)

-- |Parse top level expressions. Fails with a megaparsec error if the
-- module has no @main@ definition, instead of crashing with 'fromJust'.
parseTopLevelWithExtraModuleBindings :: [(String, AnnotatedUPT)]
                                     -> TelomareParser AnnotatedUPT
parseTopLevelWithExtraModuleBindings lst = do
  x <- getLineColumn
  bindingList <- parseAssignmentEntries
  case lookup "main" bindingList of
    Just m  -> pure $ x :< LetUPF (lst <> bindingList) m
    Nothing -> fail "missing 'main' definition"

expandAssignmentEntry :: AssignmentEntry -> [(String, AnnotatedUPT)]
expandAssignmentEntry = \case
  SingleAssignment name body -> [(name, body)]
  ListAssignment loc names body
    | isUDTAssignment names body -> expandUDT (loc :< UDTUPF names body)
    | otherwise                 -> expandPlainListAssignment loc names body

isUDTAssignment :: [String] -> AnnotatedUPT -> Bool
isUDTAssignment (name:_) (_ :< LamUPF _ _) = case name of
  firstChar:_ -> isUpper firstChar
  _           -> False
isUDTAssignment _ _ = False

expandPlainListAssignment :: LocTag -> [String] -> AnnotatedUPT -> [(String, AnnotatedUPT)]
expandPlainListAssignment loc names body =
  case listAssignmentSlots body of
    Just (slots, wrapBody)
      | length names == length slots -> zip names (wrapBody <$> slots)
      | otherwise -> error
        $ "list assignment arity mismatch: " <> show (length names)
        <> " names for " <> show (length slots) <> " values"
    Nothing ->
      let intermediate = listAssignmentIntermediate loc
          source = loc :< VarUPF intermediate
          mkAccessorBinding idx name = (name, accessAt loc idx source)
      in (intermediate, body) : zipWith mkAccessorBinding [0 ..] names

-- |Find a final list literal in a plain list assignment, preserving lambdas
-- and lets around each extracted slot. This lets `[f, g] = \x -> [...]`
-- bind `f` and `g` as functions rather than trying to project from a lambda.
listAssignmentSlots :: AnnotatedUPT -> Maybe ([AnnotatedUPT], AnnotatedUPT -> AnnotatedUPT)
listAssignmentSlots = go where
  go (l :< ListUPF xs) = Just (xs, id)
  go (l :< LetUPF binds inner) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< LetUPF binds (wrapBody expr))
  go (l :< LamUPF var inner) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< LamUPF var (wrapBody expr))
  go _ = Nothing

listAssignmentIntermediate :: LocTag -> String
listAssignmentIntermediate loc = case locStartLineColumn loc of
  Just (line, column) -> "__list_assignment_" <> show line <> "_" <> show column
  Nothing             -> "__list_assignment"

accessAt :: LocTag -> Int -> AnnotatedUPT -> AnnotatedUPT
accessAt loc 0 e = loc :< LeftUPF e
accessAt loc n e = loc :< LeftUPF (iterate (\x -> loc :< RightUPF x) e !! n)

-- |Expand a UDT declaration into a list of top-level bindings.
--
-- If the UDT body is a lambda @\\h -> ...@ (the canonical UDT idiom),
-- the expansion automatically wraps the core type representation with
-- the hash-tag mechanism (@wrapper (# wrapper)@). The shared core tuple
-- contains only the generated hash, the auto-generated validator, and
-- the first two user slots (constructor/extractor by convention).
-- Remaining slots are hoisted to normal top-level bindings so using a
-- constructor or extractor does not force every operation through sizing.
--
-- > [T, mk, unT, op1, ...] = \\h -> [ mkBody, unTBody, op1Body, ... ]
--
-- becomes (conceptually):
--
-- > __udt_T = wrapper (# wrapper)
-- >   where wrapper = \\h -> let T = validatorFor T h in [h, T, mkBody, unTBody]
-- > __udt_T_hash = left __udt_T
-- > T   = left (right __udt_T)   -- validator, usable as `(x : T)` outside
-- > mk  = left (right (right __udt_T))
-- > unT = left (right (right (right __udt_T)))
-- > op1 = let h = __udt_T_hash; T = validatorFor T h in op1Body
--
-- Non-lambda list assignments use 'expandPlainListAssignment' instead;
-- this fallback is kept for direct/internal callers of 'expandUDT'.
expandUDT :: AnnotatedUPT -> [(String, AnnotatedUPT)]
expandUDT (loc :< UDTUPF names@(tname:_) body) =
  case body of
    (_ :< LamUPF hParam inner) ->
      let (slots, wrapBody) = udtSlots tname inner
          (coreSlots, hoistedSlots) = splitAt 2 slots
          coreNames = take (1 + length coreSlots) names
          hoistedNames = drop (1 + length coreSlots) names
          validator    = autoValidator loc tname hParam
          intermediate = "__udt_" <> tname
          hashName     = intermediate <> "_hash"
          hashVar      = loc :< VarUPF hashName
          coreList     = loc :< ListUPF ((loc :< VarUPF hParam)
                                      : (loc :< VarUPF tname)
                                      : coreSlots)
          wrappedInner = loc :< LetUPF [(tname, validator)] (wrapBody coreList)
          wrapper      = loc :< LamUPF hParam wrappedInner
          udtTuple     = loc :< AppUPF wrapper (loc :< HashUPF wrapper)
          hashBinding  = (hashName, accessAt loc 0 (loc :< VarUPF intermediate))
          mkAccessorBinding idx name =
            (name, accessAt loc idx (loc :< VarUPF intermediate))
          mkHoistedBinding name slot =
            ( name
            , loc :< LetUPF [ (hParam, hashVar)
                            , (tname, validator)
                            ]
                (wrapBody slot)
            )
      in (intermediate, udtTuple)
       : hashBinding
       : zipWith mkAccessorBinding [1 ..] coreNames
      <> zipWith mkHoistedBinding hoistedNames hoistedSlots
    _ ->
      zipWith (\name idx -> (name, accessAt loc idx body)) names [0 ..]
expandUDT _ = []

-- |Find the final list literal in a UDT body and return a wrapper that
-- reapplies any surrounding lets. Hoisted methods get the same let
-- context as the core tuple, but not the sibling method bodies.
udtSlots :: String -> AnnotatedUPT -> ([AnnotatedUPT], AnnotatedUPT -> AnnotatedUPT)
udtSlots tname = go where
  go (l :< ListUPF xs) = (xs, id)
  go (l :< LetUPF binds inner) =
    let (xs, wrapBody) = go inner
    in (xs, \expr -> l :< LetUPF binds (wrapBody expr))
  go (_ :< other) = error
    $ "expandUDT: UDT body for [" <> tname
    <> "] must reduce to a list literal; got: " <> show (void other)

-- |Auto-generated validator: @\\v -> if dEqual (left v) <h> then right v else abort \"not <T>\"@.
-- Returns the validated payload on success; aborts on failure.
-- Annotated pattern lambdas use the validator's result as the case
-- scrutinee, so destructuring works on a validated value without an
-- extra ITE.
autoValidator :: LocTag -> String -> String -> AnnotatedUPT
autoValidator loc tname hParam =
  loc :< LamUPF "__udt_v"
    (loc :< ITEUPF
       (loc :< AppUPF
          (loc :< AppUPF
             (loc :< VarUPF "dEqual")
             (loc :< LeftUPF (loc :< VarUPF "__udt_v")))
          (loc :< VarUPF hParam))
       (loc :< RightUPF (loc :< VarUPF "__udt_v"))
        (loc :< AppUPF
           (loc :< VarUPF "abort")
           (loc :< StringUPF ("not " <> tname))))

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
runParseLongExpr str = bimap errorBundlePretty forget' $ runParser parseLongExpr "" str
  where
    forget' :: Cofree UnprocessedParsedTermF LocTag -> UnprocessedParsedTerm
    forget' = forget

parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePrelude str = let result = runParser parseAssignmentEntries "" str
                    in first errorBundlePretty result

-- |One parser step inside a module: returns a list because list assignments
-- expand into multiple (name, value) bindings.
parseImportOrAssignment :: TelomareParser [Either AnnotatedUPT (String, AnnotatedUPT)]
parseImportOrAssignment = do
  maybeImport <- optional $ scn *> (try parseImportQualified <|> try parseImport) <* scn
  case maybeImport of
    Nothing -> do
      maybeEntry <- optional $ scn *> try parseAssignmentEntry <* scn
      case maybeEntry of
        Nothing    -> fail "Expected either an import statement or an assignment"
        Just entry -> pure (Right <$> expandAssignmentEntry entry)
    Just imp -> pure [Left imp]

parseWithPrelude :: [(String, AnnotatedUPT)]   -- ^Prelude
                 -> String                     -- ^Raw string to be parsed
                 -> Either String AnnotatedUPT -- ^Error on Left
parseWithPrelude prelude str = first errorBundlePretty $ runParser (parseTopLevelWithExtraModuleBindings prelude) "" str

parseModule :: String -> Either String [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModule str = let result = runParser (concat <$> (scn *> many parseImportOrAssignment <* eof)) "" str
                  in first errorBundlePretty result

-- |Parse either a single expression or top level definitions defaulting to the `main` definition.
--  This function was made for telomare-evaluare
parseOneExprOrTopLevelDefs :: [(String, AnnotatedUPT)] -> TelomareParser AnnotatedUPT
parseOneExprOrTopLevelDefs extraModuleBindings =
  choice $ try <$> [ parseTopLevelWithExtraModuleBindings extraModuleBindings
                   , parseLongExpr
                   ]
