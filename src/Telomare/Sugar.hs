{-# LANGUAGE LambdaCase #-}

-- |The desugaring pass that runs immediately after parsing. The grammar in
-- 'Telomare.Parse' is deliberately dumb: it emits 'PAUPT' trees whose
-- 'SugarTermF' fragment carries the raw forms 'LamPatF' (multi-pattern
-- lambdas) and 'LetSugarF' (lets whose entries may be list assignments or
-- carry refinement annotations). 'sugarTerm' removes that fragment,
-- rewriting the raw forms into the plain
-- 'UnprocessedParsedTermL'/'LetUPF'/'CheckF' vocabulary — so the resulting
-- 'AUPT' structurally cannot contain them. Source spans are exactly what
-- the grammar alone produces.
--
-- Sugar that survives this pass ('CaseUPF', builtin names) is expanded
-- later, in 'Telomare.Desugar'.
module Telomare.Sugar
  ( SugarError (..)
  , renderSugarError
  , sugarErrorLoc
  , sugarTerm
  , sugarPattern
  , sugarDefs
  , sugarModule
  , wrapMain
  , buildMultiLambda
  ) where

import Control.Comonad.Cofree (Cofree (..))
import Control.Monad (when, (>=>))
import Data.Bifunctor (first)
import Data.Char (isUpper)
import Data.Fix (Fix (..))
import Data.Functor (void)
import Data.Functor.Foldable (embed, project)
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

-- |Errors the desugaring pass can produce. These were runtime 'error'
-- calls (or a megaparsec parse failure, for 'MissingMain') when
-- desugaring still ran inside the parser.
data SugarError
  = ListArityMismatch LocTag Int Int
    -- ^ @[a, b] = expr@ where @expr@'s final list literal has a different
    -- number of slots than there are names. Fields: location of the list
    -- assignment, number of names, number of value slots.
  | UDTBodyNotList LocTag String String
    -- ^ A UDT declaration whose lambda body does not reduce to a list
    -- literal. Fields: location, type name, description of the offending
    -- node.
  | UDTArityMismatch LocTag String Int Int
    -- ^ A UDT declaration with a different number of exported names and
    -- body slots. Fields: location, type name, number of names, body slots.
  | MissingMain
    -- ^ 'wrapMain' found no @main@ among the top-level definitions.
  deriving (Eq, Show)

renderSugarError :: SugarError -> String
renderSugarError = \case
  ListArityMismatch loc nNames nSlots ->
    "list assignment arity mismatch: " <> show nNames <> " names for "
    <> show nSlots <> " values" <> atLoc loc
  UDTBodyNotList loc tname desc ->
    "UDT body for [" <> tname <> "] must reduce to a list literal; got: "
    <> desc <> atLoc loc
  UDTArityMismatch loc tname nNames nSlots ->
    "UDT declaration for [" <> tname <> "] has " <> show nNames
    <> " names for " <> show nSlots <> " value slots; expected one type name "
    <> "plus one name per slot" <> atLoc loc
  MissingMain -> "missing 'main' definition"
  where
    atLoc loc = maybe "" (" at " <>) (renderLocTag loc)

-- |The source location a 'SugarError' points at, when it has one. Used by
-- the LSP server to attach diagnostics to a range.
sugarErrorLoc :: SugarError -> Maybe LocTag
sugarErrorLoc = \case
  ListArityMismatch loc _ _ -> Just loc
  UDTBodyNotList loc _ _   -> Just loc
  UDTArityMismatch loc _ _ _ -> Just loc
  MissingMain              -> Nothing

-- |Remove the sugar fragment, bottom-up. This is the type change that
-- guarantees no 'LamPatF' or 'LetSugarF' node survives, including inside
-- pattern annotations.
sugarTerm :: PAUPT -> Either SugarError AUPT
sugarTerm (loc :< term) = case term of
  ParsedTermSugar (LamPatF pats body) -> do
    pats' <- traverse (traverse sugarPattern) pats
    body' <- sugarTerm body
    pure $ buildMultiLambda loc pats' body'
  ParsedTermSugar (LetSugarF defs body) -> do
    bindings <- sugarDefs defs
    body' <- sugarTerm body
    pure $ loc :< LetUPF bindings body'
  ParsedTermUP upf -> do
    upf' <- traverse sugarTerm upf
    (loc :<) <$> traverseUPTPatterns sugarPattern upf'

-- |Patterns carry embedded terms in their annotations (@(v : T)@), which
-- the parser leaves raw too.
sugarPattern :: PatternP -> Either SugarError PatternA
sugarPattern (Fix pattern') = Fix <$> case pattern' of
  PatternAnnotatedF inner (AnnotatedPUPT typeExpr) ->
    PatternAnnotatedF <$> sugarPattern inner
                      <*> (AnnotatedUPT <$> sugarTerm typeExpr)
  PatternVarF name    -> pure $ PatternVarF name
  PatternIntF n       -> pure $ PatternIntF n
  PatternStringF s    -> pure $ PatternStringF s
  PatternIgnoreF      -> pure PatternIgnoreF
  PatternPairF a b    -> PatternPairF <$> sugarPattern a <*> sugarPattern b

-- |Desugar a block of raw definitions into plain (name, value) bindings.
-- Single definitions fold their refinement annotation into a 'CheckF';
-- list assignments expand into one binding per name.
sugarDefs :: [DefinitionF PAUPT] -> Either SugarError [(LocatedName, AUPT)]
sugarDefs defs = concat <$> traverse (traverse sugarTerm >=> expandDef) defs

-- |Desugar a parsed module: imports pass through, definitions expand into
-- their bindings.
sugarModule :: [ModuleItem PAUPT] -> Either SugarError [Either AUPT (String, AUPT)]
sugarModule = fmap concat . traverse item where
  item = \case
    ModuleImportItem importDecl -> pure [Left $ importDeclTerm importDecl]
    ModuleDefinitionItem def -> fmap (Right . first locatedNameText)
                                 <$> (traverse sugarTerm def >>= expandDef)

  importDeclTerm importDecl = case parsedImportQualifier importDecl of
    Nothing -> parsedImportLoc importDecl :< ImportUPF
      (locatedNameText $ parsedImportModule importDecl)
    Just qualifier -> parsedImportLoc importDecl :< ImportQualifiedUPF
      (locatedNameText qualifier)
      (locatedNameText $ parsedImportModule importDecl)

-- |Wrap a module's bindings (plus any extra module bindings, e.g. an
-- already-desugared prelude) in a let around its @main@ definition. This
-- is the semantic check that used to fail the parse itself when a module
-- had no @main@.
wrapMain :: [(String, AUPT)]       -- ^extra module bindings (e.g. prelude)
         -> [(LocatedName, AUPT)]  -- ^desugared module bindings
         -> Either SugarError AUPT
wrapMain extraModuleBindings bindings =
  case lookup "main" (first locatedNameText <$> bindings) of
    Just m -> Right $ loc :< LetUPF ((first (locatedName UnknownLoc) <$> extraModuleBindings) <> bindings) m
    Nothing -> Left MissingMain
  where
    loc = GeneratedLoc "wrapMain" Nothing

-- |Expand one definition (whose contents are already desugared) into its
-- bindings.
expandDef :: DefinitionF AUPT -> Either SugarError [(LocatedName, AUPT)]
expandDef = \case
  SingleDefF name Nothing body -> pure [(name, body)]
  SingleDefF name (Just (annotLoc, typeExpr)) body ->
    pure [(name, annotLoc :< embedH (CheckF typeExpr body))]
  ListDefF loc locatedNames body
    | isUDTAssignment names body -> expandUDTLocated loc locatedNames body
    | otherwise                  -> expandPlainListAssignment loc locatedNames body
    where
      names = locatedNameText <$> locatedNames

-- |Pick lambda-bound names for patterns. Generated names begin with an
-- underscore, which source identifiers cannot do, and the parameter index
-- keeps repeated patterns distinct.
lambdaVarNames :: [(LocTag, PatternA)] -> [LocatedName]
lambdaVarNames = zipWith nameFor [0 :: Int ..]
  where
    nameFor index (loc, pattern') = case pattern' of
      Fix (PatternVarF name) -> name
      _ -> locatedName (GeneratedLoc "lambda pattern" (Just loc))
             ("__lambda_pattern_" <> show index)

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
  let varNames = lambdaVarNames patterns
      destructured = foldr applyDestructure body (zip (snd <$> patterns) (locatedNameText <$> varNames))
      lamWrapped = foldr LamP destructured varNames
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

-- TODO rethink this
isUDTAssignment :: [String] -> AUPT -> Bool
isUDTAssignment (name:_) (LamP _ _) = case name of
  firstChar:_ -> isUpper firstChar
  _           -> False
isUDTAssignment _ _ = False

expandPlainListAssignment :: LocTag -> [LocatedName] -> AUPT -> Either SugarError [(LocatedName, AUPT)]
expandPlainListAssignment loc locatedNames body =
  case listAssignmentSlots body of
    Just (slots, wrapBody)
      | length locatedNames == length slots ->
          Right $ zipWith (\name slot -> (name, wrapBody slot)) locatedNames slots
      | otherwise -> Left $ ListArityMismatch loc (length locatedNames) (length slots)
    Nothing ->
      let intermediate = listAssignmentIntermediate loc
          source = loc :< embedL (VarF intermediate)
          mkAccessorBinding idx name = (name, accessAt loc idx source)
      in Right
       $ (locatedName (GeneratedLoc "listAssignmentIntermediate" (Just loc)) intermediate, body)
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
expandUDTLocated :: LocTag -> [LocatedName] -> AUPT -> Either SugarError [(LocatedName, AUPT)]
expandUDTLocated loc locatedNames body =
  case names of
    tname:_ -> expandUDTLocated' loc locatedNames tname body
    _       -> Right []
  where
    names = locatedNameText <$> locatedNames

expandUDTLocated' :: LocTag -> [LocatedName] -> String -> AUPT -> Either SugarError [(LocatedName, AUPT)]
expandUDTLocated' loc locatedNames tname body =
  case body of
    (LamP hParam inner) -> do
      (slots, wrapBody) <- udtSlots loc tname inner
      let nameCount = length locatedNames
          slotCount = length slots
      when (nameCount /= slotCount + 1)
        (Left $ UDTArityMismatch loc tname nameCount slotCount)
      let hParamName = locatedNameText hParam
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
      pure $ (intermediateName, udtTuple)
           : hashBinding
           : zipWith mkAccessorBinding [1 ..] coreNames
           <> zipWith mkHoistedBinding hoistedNames hoistedSlots
    _ ->
      Right $ zipWith (\name idx -> (name, accessAt loc idx body)) locatedNames [0 ..]

-- |Find the final list literal in a UDT body and return a wrapper that
-- reapplies any surrounding lets. Hoisted methods get the same let
-- context as the core tuple, but not the sibling method bodies.
udtSlots :: LocTag -> String -> AUPT -> Either SugarError ([AUPT], AUPT -> AUPT)
udtSlots loc tname = go where
  go (l :< ListUPF xs) = Right (xs, id)
  go (l :< LetUPF binds inner) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< LetUPF binds (wrapBody expr))
  go (_ :< other) = Left $ UDTBodyNotList loc tname (show (void other))

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
