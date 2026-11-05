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
import Control.Monad ((>=>))
import Data.Bifunctor (first)
import Data.Fix (Fix (..))
import Data.Foldable (traverse_)
import Data.Functor.Foldable (cata, embed, project)
import Data.Set (Set)
import qualified Data.Set as Set
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
  | DuplicatePatternVariable LocTag String
    -- ^ A pattern binds the same name twice. Fields: location of the
    -- enclosing lambda or case, the name.
  | GuardUsesOwnBinder LocTag String
    -- ^ A guard @(p : T)@ mentions a name its own pattern binds. Fields:
    -- location of the enclosing lambda or case, the name.
  | MissingMain
    -- ^ 'wrapMain' found no @main@ among the top-level definitions.
  deriving (Eq, Show)

renderExpansionError :: ExpansionError -> String
renderExpansionError = \case
  ListArityMismatch loc nNames nSlots ->
    "list assignment arity mismatch: " <> show nNames <> " names for "
    <> show nSlots <> " values" <> atLoc loc
  DuplicatePatternVariable loc name ->
    "pattern binds " <> name <> " more than once" <> atLoc loc
  GuardUsesOwnBinder loc name ->
    "a guard mentions " <> name <> ", which its own pattern binds" <> atLoc loc
  MissingMain -> "missing 'main' definition"
  where
    atLoc loc = maybe "" (" at " <>) (renderLocTag loc)

-- |The source location an 'ExpansionError' points at, when it has one. Used by
-- the LSP server to attach diagnostics to a range.
expansionErrorLoc :: ExpansionError -> Maybe LocTag
expansionErrorLoc = \case
  ListArityMismatch loc _ _ -> Just loc
  DuplicatePatternVariable loc _ -> Just loc
  GuardUsesOwnBinder loc _ -> Just loc
  MissingMain              -> Nothing

-- |Remove the sugar fragment, bottom-up. This is the type change that
-- guarantees no 'LamPatF' or 'LetSugarF' node survives, including inside
-- pattern annotations.
expandTerm :: ParsedSurfaceTerm -> Either ExpansionError ExpandedSurfaceTerm
expandTerm (loc :< term) = case term of
  ParsedTermSugar (LamPatF pats body) -> do
    pats' <- traverse (traverse expandPattern) pats
    traverse_ (uncurry checkPattern) pats'
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
      checkPattern loc pattern''
      (pattern'',) <$> expandTerm body

-- |What a pattern may not do while the scoping of its guards is undecided:
-- bind one name twice (which might later mean equality), or mention in a
-- guard a name the same pattern binds (a guard runs before the pattern's
-- variables are bound, so the name would silently mean an outer one).
checkPattern :: LocTag -> PatternA -> Either ExpansionError ()
checkPattern loc p = do
  traverse_ (Left . DuplicatePatternVariable loc) (duplicates binders)
  traverse_ (Left . GuardUsesOwnBinder loc)
    [ n | g <- guards p, n <- Set.toList (freeVars g), n `elem` binders ]
  where
    binders = locatedNameText <$> patternBinders p
    duplicates = \case
      []     -> []
      n : ns -> [n | n `elem` ns] <> duplicates (filter (/= n) ns)
    guards = cata $ \case
      PatternAnnotatedF inner (AnnotatedEST g) -> inner <> [g]
      other                                    -> concat other

-- |The names a term uses without binding them.
freeVars :: ExpandedSurfaceTerm -> Set String
freeVars (_ :< t) = case t of
  UnprocessedParsedTermL (VarF name) -> Set.singleton name
  other -> foldMapScoped
    (\bound sub -> freeVars sub `Set.difference` Set.fromList (locatedNameText <$> bound))
    other

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
    pure [(name, annotLoc :< embedH (CheckF RefinementAbort typeExpr body))]
  ListDefF loc locatedNames body -> expandPlainListAssignment loc locatedNames body

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
-- as writing @let x : T = v in body@. Annotations further in are guards of
-- the parameter's destructuring case, whose fallback aborts, so a lambda
-- parameter's guard that fails aborts as a refinement does.
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
          abort = abortTerm CaseAbort loc (loc :< StringUPF "lambda argument does not match its pattern")
      in case project p of
           PatternVarF _ -> inner
           PatternAnnotatedF innerPat (AnnotatedEST typeExpr) ->
             let checked = loc :< embedH (CheckF RefinementAbort typeExpr bound)
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
