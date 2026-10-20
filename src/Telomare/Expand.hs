{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- |The surface expansion pass that runs immediately after parsing. The grammar in
-- 'Telomare.Parse' is deliberately dumb: it emits 'ParsedSurfaceTerm' trees whose
-- 'SugarTermF' fragment carries the raw forms 'LamPatF' (multi-pattern
-- lambdas) and 'LetSugarF' (lets whose entries may be list assignments or
-- carry refinement annotations). 'expandTerm' removes that fragment,
-- rewriting the raw forms into the plain
-- 'UnprocessedParsedTermL'/'LetUPF'/'CheckF' vocabulary — so the resulting
-- 'ExpandedSurfaceTerm' structurally cannot contain them. Source spans are exactly what
-- the grammar alone produces.
--
-- Surface forms that survive this pass ('CaseUPF', builtin names) are lowered
-- later, in 'Telomare.Desugar'.
module Telomare.Expand
  ( ExpansionError (..)
  , renderExpansionError
  , expansionErrorLoc
  , expandTerm
  , expandPattern
  , expandDefs
  , expandModule
  , wrapMain
  , buildMultiLambda
  ) where

import Control.Comonad.Cofree (Cofree (..))
import Control.Monad (when, (>=>))
import Data.Bifunctor (first)
import Data.Char (isUpper)
import Data.Fix (Fix (..))
import Data.Foldable (traverse_)
import Data.Functor (void)
import Data.Functor.Foldable (cata, embed, project)
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

-- |Errors the expansion pass can produce. These were runtime 'error'
-- calls (or a megaparsec parse failure, for 'MissingMain') when
-- expansion still ran inside the parser.
data ExpansionError
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
  | MisplacedPatternAnnotation LocTag
    -- ^ A refinement annotation @(p : T)@ somewhere other than the top of
    -- a lambda parameter, e.g. inside a pair pattern or in a @case@
    -- alternative. Field: location of the enclosing lambda or case.
  | MissingMain
    -- ^ 'wrapMain' found no @main@ among the top-level definitions.
  deriving (Eq, Show)

renderExpansionError :: ExpansionError -> String
renderExpansionError = \case
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
  MisplacedPatternAnnotation loc ->
    "refinement annotations (p : T) are only supported at the top of a "
    <> "lambda parameter" <> atLoc loc
  MissingMain -> "missing 'main' definition"
  where
    atLoc loc = maybe "" (" at " <>) (renderLocTag loc)

-- |The source location an 'ExpansionError' points at, when it has one. Used by
-- the LSP server to attach diagnostics to a range.
expansionErrorLoc :: ExpansionError -> Maybe LocTag
expansionErrorLoc = \case
  ListArityMismatch loc _ _ -> Just loc
  UDTBodyNotList loc _ _   -> Just loc
  UDTArityMismatch loc _ _ _ -> Just loc
  MisplacedPatternAnnotation loc -> Just loc
  MissingMain              -> Nothing

-- |Remove the sugar fragment, bottom-up. This is the type change that
-- guarantees no 'LamPatF' or 'LetSugarF' node survives, including inside
-- pattern annotations.
expandTerm :: ParsedSurfaceTerm -> Either ExpansionError ExpandedSurfaceTerm
expandTerm (loc :< term) = case term of
  ParsedTermSugar (LamPatF pats body) -> do
    pats' <- traverse (traverse expandPattern) pats
    traverse_ checkLambdaPattern pats'
    body' <- expandTerm body
    pure $ buildMultiLambda loc pats' body'
  ParsedTermSugar (LetSugarF defs body) -> do
    bindings <- expandDefs defs
    body' <- expandTerm body
    pure $ loc :< LetUPF bindings body'
  ParsedTermUP (CaseUPF scrutinee alternatives) -> do
    scrutinee' <- expandTerm scrutinee
    alternatives' <- traverse expandAlternative alternatives
    pure $ loc :< CaseUPF scrutinee' alternatives'
  ParsedTermUP upf -> do
    upf' <- traverse expandTerm upf
    (loc :<) <$> traverseUPTPatterns expandPattern upf'
  where
    expandAlternative (pattern', body) = do
      pattern'' <- expandPattern pattern'
      checkPlainPattern loc pattern''
      (pattern'',) <$> expandTerm body

-- |A lambda parameter may be wrapped in refinement annotations, but the
-- pattern underneath must be plain: 'buildMultiLambda' only lowers
-- annotations at the top, and 'Telomare.Desugar' would drop any others.
checkLambdaPattern :: (LocTag, PatternA) -> Either ExpansionError ()
checkLambdaPattern (loc, p) = case project p of
  PatternAnnotatedF inner _ -> checkLambdaPattern (loc, inner)
  _                         -> checkPlainPattern loc p

-- |Reject a pattern that contains a refinement annotation anywhere.
checkPlainPattern :: LocTag -> PatternA -> Either ExpansionError ()
checkPlainPattern loc p = when (hasAnnotation p) . Left $ MisplacedPatternAnnotation loc
  where
    hasAnnotation = cata $ \case
      PatternAnnotatedF _ _ -> True
      other                 -> or other

-- |Patterns carry embedded terms in their annotations (@(v : T)@), which
-- the parser leaves raw too.
expandPattern :: PatternP -> Either ExpansionError PatternA
expandPattern (Fix pattern') = Fix <$> case pattern' of
  PatternAnnotatedF inner (AnnotatedPST typeExpr) ->
    PatternAnnotatedF <$> expandPattern inner
                       <*> (AnnotatedEST <$> expandTerm typeExpr)
  PatternVarF name    -> pure $ PatternVarF name
  PatternIntF n       -> pure $ PatternIntF n
  PatternStringF s    -> pure $ PatternStringF s
  PatternIgnoreF      -> pure PatternIgnoreF
  PatternPairF a b    -> PatternPairF <$> expandPattern a <*> expandPattern b

-- |Expand a block of raw definitions into plain (name, value) bindings.
-- Single definitions fold their refinement annotation into a 'CheckF';
-- list assignments expand into one binding per name.
expandDefs :: [DefinitionF ParsedSurfaceTerm] -> Either ExpansionError [(LocatedName, ExpandedSurfaceTerm)]
expandDefs defs = concat <$> traverse (traverse expandTerm >=> expandDef) defs

-- |Expand a parsed module: imports pass through, definitions expand into
-- their bindings.
expandModule :: [ModuleItem ParsedSurfaceTerm] -> Either ExpansionError ExpandedModule
expandModule = fmap concat . traverse item where
  item = \case
    ModuleImportItem importDecl -> pure [ExpandedModuleImport importDecl]
    ModuleDefinitionItem def -> fmap (uncurry ExpandedModuleBinding)
                                 <$> (traverse expandTerm def >>= expandDef)

-- |Wrap a module's bindings (plus any extra module bindings, e.g. an
-- already-expanded prelude) in a let around its @main@ definition. This
-- is the semantic check that used to fail the parse itself when a module
-- had no @main@.
wrapMain :: [(String, ExpandedSurfaceTerm)]       -- ^extra module bindings (e.g. prelude)
         -> [(LocatedName, ExpandedSurfaceTerm)]  -- ^expanded module bindings
         -> Either ExpansionError ExpandedSurfaceTerm
wrapMain extraModuleBindings bindings =
  case lookup "main" (first locatedNameText <$> bindings) of
    Just m -> Right $ loc :< LetUPF ((first (locatedName UnknownLoc) <$> extraModuleBindings) <> bindings) m
    Nothing -> Left MissingMain
  where
    loc = GeneratedLoc "wrapMain" Nothing

-- |Expand one definition (whose contents are already expanded) into its
-- bindings.
expandDef :: DefinitionF ExpandedSurfaceTerm -> Either ExpansionError [(LocatedName, ExpandedSurfaceTerm)]
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
-- > \\v1 -> \\v2 -> \\v3 -> applyDestructure p1 v1
-- >                          (applyDestructure p2 v2
-- >                            (applyDestructure p3 v3 body))
--
-- where @applyDestructure p v body@ is @body@ when @p@ is a 'PatternVar'
-- (no destructure needed) and a @case v of p -> body@ otherwise. Earlier
-- parameters' bindings are in scope in later parameters' annotations.
--
-- A refinement annotation @(p : T)@ binds the checked value, so
-- @\\(x : T) -> body@ becomes @\\v -> let x = CheckF T v in body@, the same
-- as writing @let x : T = v in body@. 'checkLambdaPattern' guarantees
-- annotations only occur at the top of a parameter.
--
-- This avoids putting a function-valued lambda inside a case body, which
-- would cause the case-rewrite to type-mismatch against the (Pair-typed)
-- abort fallback.
buildMultiLambda :: LocTag -> [(LocTag, PatternA)] -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
buildMultiLambda lt patterns body =
  let varNames = lambdaVarNames patterns
      destructured = foldr applyDestructure body (zip patterns (locatedNameText <$> varNames))
      lamWrapped = foldr LamP destructured varNames
  in lamWrapped
  where
    applyDestructure ((loc, p), varName) inner =
      let bound = lt :< embedL (VarF varName)
          abort = AppP
                    (lt :< embedL (VarF "abort"))
                    (lt :< StringUPF "buildMultiLambda: pattern not reached")
      in case project p of
           PatternVarF _ -> inner
           PatternAnnotatedF innerPat (AnnotatedEST typeExpr) ->
             let checked = loc :< embedH (CheckF typeExpr bound)
             in case project innerPat of
                  PatternVarF name -> lt :< LetUPF [(name, checked)] inner
                  _ ->
                    let checkedName = varName <> "_checked"
                        checkedBinder = locatedName (GeneratedLoc "annotated lambda pattern" (Just loc)) checkedName
                    in lt :< LetUPF [(checkedBinder, checked)]
                         (applyDestructure ((loc, innerPat), checkedName) inner)
           _ ->
             lt :< CaseUPF bound
               [ (p, inner)
               , (embed PatternIgnoreF, abort)
               ]

-- TODO rethink this
isUDTAssignment :: [String] -> ExpandedSurfaceTerm -> Bool
isUDTAssignment (name:_) (LamP _ _) = case name of
  firstChar:_ -> isUpper firstChar
  _           -> False
isUDTAssignment _ _ = False

expandPlainListAssignment :: LocTag -> [LocatedName] -> ExpandedSurfaceTerm -> Either ExpansionError [(LocatedName, ExpandedSurfaceTerm)]
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
listAssignmentSlots :: ExpandedSurfaceTerm -> Maybe ([ExpandedSurfaceTerm], ExpandedSurfaceTerm -> ExpandedSurfaceTerm)
listAssignmentSlots = go where
  go (_l :< ListUPF xs) = Just (xs, id)
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

accessAt :: LocTag -> Int -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
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
-- > T   = left (right __udt_T)   -- validator, callable as `T x` outside
-- > mk  = left (right (right __udt_T))
-- > unT = left (right (right (right __udt_T)))
-- > op1 = let h = __udt_T_hash; T = validatorFor T h in op1Body
expandUDTLocated :: LocTag -> [LocatedName] -> ExpandedSurfaceTerm -> Either ExpansionError [(LocatedName, ExpandedSurfaceTerm)]
expandUDTLocated loc locatedNames body =
  case names of
    tname:_ -> expandUDTLocated' loc locatedNames tname body
    _       -> Right []
  where
    names = locatedNameText <$> locatedNames

expandUDTLocated' :: LocTag -> [LocatedName] -> String -> ExpandedSurfaceTerm -> Either ExpansionError [(LocatedName, ExpandedSurfaceTerm)]
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
udtSlots :: LocTag -> String -> ExpandedSurfaceTerm -> Either ExpansionError ([ExpandedSurfaceTerm], ExpandedSurfaceTerm -> ExpandedSurfaceTerm)
udtSlots loc tname = go where
  go (_l :< ListUPF xs) = Right (xs, id)
  go (l :< LetUPF binds inner) = do
    (xs, wrapBody) <- go inner
    pure (xs, \expr -> l :< LetUPF binds (wrapBody expr))
  go (_ :< other) = Left $ UDTBodyNotList loc tname (show (void other))

-- |Auto-generated validator: @\\v -> if dEqual (left v) <h> then right v else abort \"not <T>\"@.
-- Returns the validated payload on success; aborts on failure.
-- Call it directly (@\\v -> let x = T v in ...@) to unwrap a branded value.
autoValidator :: LocTag -> String -> String -> ExpandedSurfaceTerm
autoValidator loc tname hParam =
  LamP (locatedName (GeneratedLoc "UDT validator" (Just loc)) "__udt_v")
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
