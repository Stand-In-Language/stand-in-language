{-# LANGUAGE LambdaCase #-}

-- |The desugaring pass that runs immediately after parsing. The grammar in
-- 'Telomare.Parse' is deliberately dumb: it emits the raw forms
-- 'LamPatUPF' (multi-pattern lambdas), 'LetSugarUPF' (lets whose entries
-- may be list assignments or carry refinement annotations) and 'UDTUPF'.
-- 'desugarTerm' eliminates all three, rewriting them into the plain
-- 'UnprocessedParsedTermL'/'LetUPF'/'CheckF' vocabulary every later stage
-- consumes. Everything here is a pure @AUPT@ builder, so source spans are
-- exactly what the grammar alone produces.
--
-- Sugar that survives this pass ('CaseUPF', builtin names) is expanded
-- later, in 'Telomare.Desugar'.
module Telomare.Sugar
  ( SugarError (..)
  , renderSugarError
  , sugarErrorLoc
  , desugarTerm
  , desugarDefs
  , desugarModule
  , wrapMain
  , buildMultiLambda
  ) where

import Control.Comonad.Cofree (Cofree (..))
import Control.Monad ((>=>))
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
  MissingMain -> "missing 'main' definition"
  where
    atLoc loc = maybe "" (" at " <>) (renderLocTag loc)

-- |The source location a 'SugarError' points at, when it has one. Used by
-- the LSP server to attach diagnostics to a range.
sugarErrorLoc :: SugarError -> Maybe LocTag
sugarErrorLoc = \case
  ListArityMismatch loc _ _ -> Just loc
  UDTBodyNotList loc _ _   -> Just loc
  MissingMain              -> Nothing

-- |Rewrite away every raw form, bottom-up. The result contains no
-- 'LamPatUPF', 'LetSugarUPF' or 'UDTUPF' nodes, including inside pattern
-- annotations.
desugarTerm :: AUPT -> Either SugarError AUPT
desugarTerm (loc :< term) = case term of
  LamPatUPF pats body -> do
    pats' <- traverse (traverse desugarPattern) pats
    body' <- desugarTerm body
    pure $ buildMultiLambda loc pats' body'
  LetSugarUPF defs body -> do
    bindings <- desugarDefs defs
    body' <- desugarTerm body
    pure $ loc :< LetUPF bindings body'
  CaseUPF scrutinee alternatives -> do
    scrutinee' <- desugarTerm scrutinee
    alternatives' <- traverse (\(p, b) -> (,) <$> desugarPattern p <*> desugarTerm b) alternatives
    pure $ loc :< CaseUPF scrutinee' alternatives'
  other -> (loc :<) <$> traverse desugarTerm other

-- |Patterns carry embedded terms in their annotations (@(v : T)@), which
-- the parser now leaves raw too.
desugarPattern :: PatternA -> Either SugarError PatternA
desugarPattern (Fix pattern') = case pattern' of
  PatternAnnotatedF inner (AnnotatedUPT typeExpr) ->
    fmap Fix $ PatternAnnotatedF <$> desugarPattern inner
                                 <*> (AnnotatedUPT <$> desugarTerm typeExpr)
  other -> Fix <$> traverse desugarPattern other

-- |Desugar a block of raw definitions into plain (name, value) bindings.
-- Single definitions fold their refinement annotation into a 'CheckF';
-- list assignments expand into one binding per name.
desugarDefs :: [DefinitionF AUPT] -> Either SugarError [(LocatedName, AUPT)]
desugarDefs defs = concat <$> traverse (traverse desugarTerm >=> expandDef) defs

-- |Desugar a parsed module: imports pass through, definitions expand into
-- their bindings.
desugarModule :: [Either AUPT (DefinitionF AUPT)] -> Either SugarError [Either AUPT (String, AUPT)]
desugarModule = fmap concat . traverse item where
  item = \case
    Left imp -> (: []) . Left <$> desugarTerm imp
    Right def -> fmap (Right . first locatedNameText)
                 <$> (traverse desugarTerm def >>= expandDef)

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
