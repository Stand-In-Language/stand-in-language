{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Telomare.Parser where

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
import PrettyPrint (indentSansFirstLine)
import qualified System.IO.Strict as Strict
import Telomare
import Telomare.TypeChecker (typeCheck)
import Text.Megaparsec (MonadParsec (eof, notFollowedBy, try), ParseErrorBundle,
                        Parsec, Pos, SourcePos (sourceColumn, sourceLine),
                        between, choice, errorBundlePretty, getOffset,
                        getSourcePos, many, manyTill, optional, runParser,
                        sepBy, some, unPos, (<?>), (<|>))
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Pos (Pos)
import Text.Read (readMaybe)
import Text.Show.Deriving (deriveShow1)

data AssignmentEntry
  = SingleAssignment LocatedName AUPT
  | ListAssignment LocTag [LocatedName] AUPT

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
  { sourceSpanFile = Nothing
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

-- |Generate a fresh-looking variable name from a pattern's shape, used
-- as the name of the lambda parameter that 'buildMultiLambda' introduces
-- before destructuring.
genPatternVarName :: PatternA -> String
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
lambdaVarName :: (LocTag, PatternA) -> LocatedName
lambdaVarName (loc, pattern') = case pattern' of
  Fix (PatternVarF str) -> locatedName loc str
  p              -> locatedName (GeneratedLoc "lambda pattern" (Just loc)) (genPatternVarName p)

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
buildMultiLambda :: LocTag -> [(LocTag, PatternA)] -> AUPT -> AUPT
buildMultiLambda lt patterns body =
  let varNames = lambdaVarName <$> patterns
      destructured = foldr applyDestructure body (zip (snd <$> patterns) (locatedNameText <$> varNames))
      lamWrapped = foldr (\v inner -> LamP v inner) destructured varNames
  in lamWrapped
  where
    applyDestructure (p, varName) inner =
      let bound = lt :< embedL (VarF varName)
          abort = AppP
                    (lt :< embedL (VarF "abort"))
                    (lt :< StringUPF "buildMultiLambda: pattern not reached")
      in case project p of
           PatternVarF _ -> inner
           PatternAnnotatedF innerPat typeExpr ->
             -- Use the validator result as the case scrutinee instead of
             -- CheckUPF: hash-based UDT validators are runtime values that
             -- the static refinement analyzer cannot symbolically evaluate.
             let tyApplied = AppP (unAnnotatedUPT typeExpr) bound
             in lt :< CaseUPF tyApplied [(innerPat, inner)]
           _ ->
             lt :< CaseUPF bound
               [ (p, inner)
               , (embed PatternIgnoreF, abort)
               ]

-- |Build a single-argument lambda with optional destructuring.
-- Kept as a thin wrapper around 'buildMultiLambda' so existing callers
-- that work pattern-at-a-time continue to function.
makeLambda :: LocTag -> PatternA -> AUPT -> AUPT
makeLambda lt p = buildMultiLambda lt [(lt, p)]

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

expandAssignmentEntry :: AssignmentEntry -> [(LocatedName, AUPT)]
expandAssignmentEntry = \case
  SingleAssignment name body -> [(name, body)]
  ListAssignment loc locatedNames body
    | isUDTAssignment names body -> expandUDTLocated loc locatedNames body
    | otherwise                 -> expandPlainListAssignment loc locatedNames body
    where
      names = locatedNameText <$> locatedNames

-- TODO rethink this
isUDTAssignment :: [String] -> AUPT -> Bool
isUDTAssignment (name:_) (LamP _ _) = case name of
  firstChar:_ -> isUpper firstChar
  _           -> False
isUDTAssignment _ _ = False

expandPlainListAssignment :: LocTag -> [LocatedName] -> AUPT -> [(LocatedName, AUPT)]
expandPlainListAssignment loc locatedNames body =
  case listAssignmentSlots body of
    Just (slots, wrapBody)
      | length locatedNames == length slots ->
          zipWith (\name slot -> (name, wrapBody slot)) locatedNames slots
      | otherwise -> error
        $ "list assignment arity mismatch: " <> show (length locatedNames)
        <> " names for " <> show (length slots) <> " values"
    Nothing ->
      let intermediate = listAssignmentIntermediate loc
          source = loc :< embedL (VarF intermediate)
          mkAccessorBinding idx name = (name, accessAt loc idx source)
      in (locatedName (GeneratedLoc "listAssignmentIntermediate" (Just loc)) intermediate, body)
       : zipWith mkAccessorBinding [0 ..] locatedNames

-- |Find a final list literal in a plain list assignment, preserving lambdas
-- and lets around each extracted slot. This lets `[f, g] = \x -> [...]`
-- bind `f` and `g` as functions rather than trying to project from a lambda.
listAssignmentSlots :: AUPT -> Maybe ([AUPT], AUPT -> AUPT)
listAssignmentSlots = go where
  go (l :< ListUPF xs) = Just (xs, id)
  go (l :< LetUPF binds inner) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< LetUPF binds (wrapBody expr))
  go (l :< UnprocessedParsedTermL (LamF var inner)) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< embedL (LamF var (wrapBody expr)))
  go _ = Nothing

listAssignmentIntermediate :: LocTag -> String
listAssignmentIntermediate loc = case locStartLineColumn loc of
  Just (line, column) -> "__list_assignment_" <> show line <> "_" <> show column
  Nothing             -> "__list_assignment"

accessAt :: LocTag -> Int -> AUPT -> AUPT
accessAt loc 0 e = loc :< embedH (HLeftF e)
accessAt loc n e = loc :< embedH (HLeftF (iterate (\x -> loc :< embedH (HRightF x)) e !! n))

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
expandUDT :: AUPT -> [(String, AUPT)]
expandUDT (loc :< UDTUPF names@(tname:_) body) =
  first locatedNameText <$> expandUDTLocated loc (locatedName loc <$> names) body
expandUDT _ = []

expandUDTLocated :: LocTag -> [LocatedName] -> AUPT -> [(LocatedName, AUPT)]
expandUDTLocated loc locatedNames body =
  case names of
    tname:_ -> expandUDTLocated' loc locatedNames tname body
    _       -> []
  where
    names = locatedNameText <$> locatedNames

expandUDTLocated' :: LocTag -> [LocatedName] -> String -> AUPT -> [(LocatedName, AUPT)]
expandUDTLocated' loc locatedNames tname body =
  case body of
    (LamP hParam inner) ->
      let (slots, wrapBody) = udtSlots tname inner
          hParamName = locatedNameText hParam
          (coreSlots, hoistedSlots) = splitAt 2 slots
          coreNames = take (1 + length coreSlots) locatedNames
          hoistedNames = drop (1 + length coreSlots) locatedNames
          validator    = autoValidator loc tname hParamName
          intermediate = "__udt_" <> tname
          hashName     = intermediate <> "_hash"
          hashVar      = loc :< embedL (VarF hashName)
          coreList     = loc :< ListUPF ((loc :< embedL (VarF hParamName))
                                      : (loc :< embedL (VarF tname))
                                      : coreSlots)
          wrappedInner = loc :< LetUPF [(locatedName loc tname, validator)] (wrapBody coreList)
          wrapper      = LamP hParam wrappedInner
          udtTuple     = AppP wrapper (loc :< embedH (HashF wrapper))
          generated parent name = locatedName (GeneratedLoc name (Just parent)) name
          hashBinding  = (generated loc hashName, accessAt loc 0 (loc :< embedL (VarF intermediate)))
          mkAccessorBinding idx name =
            (name, accessAt loc idx (loc :< embedL (VarF intermediate)))
          mkHoistedBinding name slot =
            ( name
            , loc :< LetUPF [ (locatedName (locatedNameLoc hParam) hParamName, hashVar)
                            , (locatedName loc tname, validator)
                            ]
                (wrapBody slot)
            )
          intermediateName = generated loc intermediate
      in (intermediateName, udtTuple)
       : hashBinding
       : zipWith mkAccessorBinding [1 ..] coreNames
       <> zipWith mkHoistedBinding hoistedNames hoistedSlots
    _ ->
      zipWith (\name idx -> (name, accessAt loc idx body)) locatedNames [0 ..]

-- |Find the final list literal in a UDT body and return a wrapper that
-- reapplies any surrounding lets. Hoisted methods get the same let
-- context as the core tuple, but not the sibling method bodies.
udtSlots :: String -> AUPT -> ([AUPT], AUPT -> AUPT)
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
autoValidator :: LocTag -> String -> String -> AUPT
autoValidator loc tname hParam =
  LamP (locatedName (GeneratedLoc "annotated pattern lambda" (Just loc)) "__udt_v")
    (ITEP
       (AppP
          (AppP
             (loc :< embedL (VarF "dEqual"))
             (loc :< embedH (HLeftF (loc :< embedL (VarF "__udt_v")))))
          (loc :< embedL (VarF hParam)))
       (loc :< embedH (HRightF (loc :< embedL (VarF "__udt_v"))))
        (AppP
           (loc :< embedL (VarF "abort"))
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
runParseLongExpr str = bimap errorBundlePretty convert $ runParser parseLongExpr "" str
  where
    convert = UnprocessedParsedTerm . cata f where
      f :: C.CofreeF (UnprocessedParsedTermF PatternA) LocTag (Fix (UnprocessedParsedTermF Pattern)) -> Fix (UnprocessedParsedTermF Pattern)
      f (_ C.:< f') = embed $ case f' of
        UnprocessedParsedTermB x  -> UnprocessedParsedTermB x
        UnprocessedParsedTermH x  -> UnprocessedParsedTermH x
        LetUPF bindings x         -> LetUPF bindings x
        ListUPF x                 -> ListUPF x
        IntUPF n                  -> IntUPF n
        StringUPF s               -> StringUPF s
        UDTUPF names x            -> UDTUPF names x
        CaseUPF x matches         -> CaseUPF x $ fmap cp matches
        ImportQualifiedUPF a b    -> ImportQualifiedUPF a b
        ImportUPF s               -> ImportUPF s
      cp (p, b) = (cata (embed . pf) p, b)
      pf = \case
        PatternVarF s ->PatternVarF s
        PatternAnnotatedF x (AnnotatedUPT t) -> PatternAnnotatedF x (UnprocessedParsedTerm $ cata f t)
        PatternIntF n -> PatternIntF n
        PatternStringF s -> PatternStringF s
        PatternIgnoreF -> PatternIgnoreF
        PatternPairF a b -> PatternPairF a b

parsePrelude :: String -> Either String [(String, AnnotatedUPT)]
parsePrelude str = let result = runParser parseAssignmentEntries "" str
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
parseModule str = first errorBundlePretty $ parseModuleDetailed str

parseModuleDetailed :: String -> Either (ParseErrorBundle String Void) [Either AnnotatedUPT (String, AnnotatedUPT)]
parseModuleDetailed = wrapUp . runParser (concat <$> (scn *> many parseImportOrAssignment <* eof)) "" where
  wrapUp = second (fmap (bimap AnnotatedUPT (second AnnotatedUPT)))

-- |Parse either a single expression or top level definitions defaulting to the `main` definition.
--  This function was made for telomare-evaluare
parseOneExprOrTopLevelDefs :: [(String, AUPT)] -> TelomareParser AUPT
parseOneExprOrTopLevelDefs extraModuleBindings =
  choice $ try <$> [ parseTopLevelWithExtraModuleBindings extraModuleBindings
                   , parseLongExpr
                   ]
