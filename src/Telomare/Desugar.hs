{-# LANGUAGE LambdaCase #-}

-- |Post-parse desugaring. Case expressions are lowered to nested if/else
-- chains by the type-changing 'desugarTerm' boundary,
-- builtin names are bound ('addBuiltins') and partially applied builtins
-- are rewritten to direct forms ('optimizeBuiltinFunctions').
--
-- Raw parse-level sugar (multi-pattern lambdas, list assignments) is
-- expanded before this stage runs, by 'Telomare.Expand'.
module Telomare.Desugar
  ( desugarTerm
  , patternToTerm
  , optimizeBuiltinFunctions
  ) where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Data.Bifunctor (first, second)
import Data.Function (on)
import Data.Functor.Foldable (Recursive (..))
import Data.List (nubBy)
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

-- |A path from the root of a matched term to one of its subterms: a
-- composition of 'HLeft' and 'HRight'.
type Path = DesugaredSurfaceTerm -> DesugaredSurfaceTerm

-- |The exact structure a pattern requires of a matched value. A value
-- matches a literal only if it is the literal's encoding, node for node.
data Shape
  = AnyShape -- ^ A variable or ignore: anything matches
  | ZeroShape
  | PairShape Shape Shape
  | IntShape Int -- ^ A positive integer literal
  | StringShape String -- ^ A non-empty string literal

-- |The pattern's structure. Zero and the empty string are both encoded as
-- zero.
patternShape :: PatternA -> Shape
patternShape = cata $ \case
  PatternPairF x y      -> PairShape x y
  PatternIntF 0         -> ZeroShape
  PatternIntF i         -> IntShape i
  PatternStringF ""     -> ZeroShape
  PatternStringF str    -> StringShape str
  PatternVarF _         -> AnyShape
  PatternIgnoreF        -> AnyShape
  PatternAnnotatedF x _ -> x

-- |The parts of a pattern that bind or test beyond its structure.
data PatternNode
  = VarNode LocatedName
  | GuardNode DesugaredSurfaceTerm -- ^ The predicate must hold of the term here

-- |Every variable and guard of a pattern, in left-to-right preorder, with
-- the path to it from the root. A guard comes after the nodes of the
-- pattern it annotates, and the paths to variables under a guard pass
-- through a refinement check of it.
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) (PatternVar "y"))
--      will return [(HLeft, VarNode "x"), (HRight . HRight, VarNode "y")]
patternNodes :: PatternA -> [(Path, PatternNode)]
patternNodes = cata alg where
  alg = \case
    PatternPairF x y -> (first (. HLeft) <$> x) <> (first (. HRight) <$> y)
    PatternVarF name -> [(id, VarNode name)]
    PatternAnnotatedF x (AnnotatedEST g) ->
      let guard = lowerCases g
      in (refineVar guard <$> x) <> [(id, GuardNode guard)]
    PatternIntF _    -> []
    PatternStringF _ -> []
    PatternIgnoreF   -> []
  -- A variable under a guard is bound through a refinement check of the
  -- guarded term. The match already tested the guard, so the check cannot
  -- fail, but it lets sizing bound the variable as a let refinement would.
  refineVar g (path, VarNode name) = (path . refined g, VarNode name)
  refineVar _ node                 = node
  refined g t@(anno :< _) = anno :< UnprocessedParsedTermH (CheckF RefinementAbort g t)

-- |Realize a pattern's literal skeleton as a term, with variables and
-- ignores as zeroes. Polymorphic in the case witness and pattern parameter
-- so both the expanded and desugared phases can use it.
patternToTerm :: LocTag -> PatternA -> Cofree (UnprocessedParsedTermF c p) LocTag
patternToTerm anno = cata alg where
  alg = \case
    PatternPairF x y       -> anno :< embedB (PairSF x y)
    PatternIntF i          -> anno :< IntUPF i
    PatternStringF str     -> anno :< StringUPF str
    PatternVarF _          -> anno :< IntUPF 0
    PatternIgnoreF         -> anno :< IntUPF 0
    PatternAnnotatedF x _  -> x

-- |Lower a case expression to nested if/else chains that try each
-- alternative in order, aborting when none matches. A scrutinee that is not
-- already a variable is bound once, to a name source code cannot write, so
-- the checks and bindings refer to it rather than copying it.
--
-- Matching depends on no definitions from source: literals are compared by
-- the 'caseHelpers' that 'addBuiltins' binds.
caseToNestedIfs :: LocTag -- ^ Where the case is, for its abort
                -> DesugaredSurfaceTerm -- ^ Term to be pattern matched
                -> [(PatternA, DesugaredSurfaceTerm)] -- ^ Alternatives
                -> DesugaredSurfaceTerm
caseToNestedIfs caseLoc scrutinee@(anno :< _) alternatives = case scrutinee of
  VarP _ -> lower scrutinee
  _      -> app generated (lam generated scrutineeName (lower (var generated scrutineeName)))
                scrutinee
  where
    generated = GeneratedLoc "case scrutinee" (Just anno)
    scrutineeName = "__case_scrutinee"
    lower x = foldr (alternative x) nonExhaustive alternatives
    nonExhaustive =
      ite caseLoc (int caseLoc 1)
          (abortTerm CaseAbort caseLoc (caseLoc :< StringUPF "Non-exhaustive patterns in case"))
          (int caseLoc 0)
    -- An alternative without checks always matches, so later ones are dropped.
    alternative x (p, result@(resultAnno :< _)) next =
      let nodes = patternNodes p
          bound = bindPatternVars x nodes result
      in case matchChecks resultAnno x (patternShape p) nodes of
        []     -> bound
        checks -> ite resultAnno (allOf resultAnno checks) bound next

-- |Checks, each nonzero when it passes, that the term has the pattern's
-- structure and then that its guards hold. Structure comes first, so a
-- guard only sees a term the rest of the pattern matches.
matchChecks :: LocTag -> DesugaredSurfaceTerm -> Shape -> [(Path, PatternNode)]
            -> [DesugaredSurfaceTerm]
matchChecks anno x shape nodes =
  catMaybes [shapeCheck anno x shape]
    <> [ app anno g (path x) | (path, GuardNode g) <- nodes ]

-- |A check that the term has the shape, or Nothing when any term does. A
-- pair is tested before its parts, which are tested left to right. The
-- literal goes first to a helper: the helpers recurse on their first
-- argument, and the scrutinee may be unbounded input.
shapeCheck :: LocTag -> DesugaredSurfaceTerm -> Shape -> Maybe DesugaredSurfaceTerm
shapeCheck anno = check where
  check t = \case
    AnyShape      -> Nothing
    ZeroShape     -> Just $ isZero anno t
    PairShape l r -> Just $
      case catMaybes [check (left anno t) l, check (right anno t) r] of
        []    -> t
        parts -> ite anno t (allOf anno parts) (int anno 0)
    IntShape i    -> Just $ app anno (app anno (var anno intEqualName) (int anno i)) t
    StringShape s -> Just $ app anno (app anno (var anno stringEqualName) (anno :< StringUPF s)) t

-- |The conjunction of non-empty checks, nonzero exactly when all of them
-- are: each check guards the rest.
allOf :: LocTag -> [DesugaredSurfaceTerm] -> DesugaredSurfaceTerm
allOf anno = \case
  [c]      -> c
  (c : cs) -> ite anno c (allOf anno cs) (int anno 0)
  []       -> int anno 1

-- |Bind each pattern variable in the case result to its part of the term,
-- as an applied lambda. The leftmost occurrence of a repeated variable wins.
bindPatternVars :: DesugaredSurfaceTerm -> [(Path, PatternNode)] -> DesugaredSurfaceTerm
                -> DesugaredSurfaceTerm
bindPatternVars x nodes result = foldr bind result vars where
  vars = nubBy ((==) `on` (locatedNameText . fst)) [ (name, path x) | (path, VarNode name) <- nodes ]
  bind :: (LocatedName, DesugaredSurfaceTerm) -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
  bind (name, value) body = AppP (LamP name body) value

intEqualName, stringEqualName :: String
intEqualName = "__case_intEqual"
stringEqualName = "__case_stringEqual"

-- |Exact equality with a literal, for case matching: each helper takes the
-- literal first and recurses on it alone. An integer @n@ is encoded as
-- @n - 1@ paired with zero, so its helper walks the left spine of both
-- terms and requires every right of the other to be zero. A string is a
-- zero-terminated list of character codes, compared code by code.
caseHelpers :: [(String, ExpandedSurfaceTerm)]
caseHelpers =
  [ (intEqualName, walkLiteral intEqualName (\loc p -> isZero loc (right loc (right loc p))) left)
  , (stringEqualName, walkLiteral stringEqualName sameHead right)
  ]
  where
    sameHead loc p = app loc (app loc (var loc intEqualName) (left loc (left loc p)))
                             (left loc (right loc p))
    -- With the literal and the other term paired as @p@: while the literal
    -- is a pair, the other must be one whose head matches, and the walk
    -- continues on the next parts of both; once the literal is zero, so must
    -- the other be.
    walkLiteral name headMatches next =
      lam loc "literal" . lam loc "term" $
        app loc walk (pair loc (var loc "literal") (var loc "term"))
      where
        loc = GeneratedLoc ("case helper " <> name) Nothing
        walk = loc :< UnprocessedParsedTermH (RecursionF test step base)
        test = lam loc "p" (left loc (var loc "p"))
        step = lam loc "recur" . lam loc "p" $
          let p = var loc "p"
          in ite loc (right loc p)
                 (ite loc (headMatches loc p)
                      (app loc (var loc "recur") (pair loc (next loc (left loc p)) (next loc (right loc p))))
                      (int loc 0))
                 (int loc 0)
        base = lam loc "p" (isZero loc (right loc (var loc "p")))

-- Builders for generated terms, each placed at the given location.

type Term c p = Cofree (UnprocessedParsedTermF c p) LocTag

ite :: LocTag -> Term c p -> Term c p -> Term c p -> Term c p
ite anno c t e = anno :< UnprocessedParsedTermH (ITEF c t e)

-- |One when the term is zero, else zero.
isZero :: LocTag -> Term c p -> Term c p
isZero anno t = ite anno t (int anno 0) (int anno 1)

left, right :: LocTag -> Term c p -> Term c p
left anno t = anno :< UnprocessedParsedTermH (HLeftF t)
right anno t = anno :< UnprocessedParsedTermH (HRightF t)

pair :: LocTag -> Term c p -> Term c p -> Term c p
pair anno a b = anno :< UnprocessedParsedTermB (PairSF a b)

app :: LocTag -> Term c p -> Term c p -> Term c p
app anno f x = anno :< UnprocessedParsedTermL (AppF f x)

lam :: LocTag -> String -> Term c p -> Term c p
lam anno name body = anno :< UnprocessedParsedTermL (LamF (locatedName anno name) body)

var :: LocTag -> String -> Term c p
var anno name = anno :< UnprocessedParsedTermL (VarF name)

int :: LocTag -> Int -> Term c p
int anno n = anno :< IntUPF n

-- |Run every post-sugar rewrite and remove the case capability from the term
-- type before resolution.
desugarTerm :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
desugarTerm = lowerCases
            . optimizeBuiltinFunctions
            . addBuiltins

lowerCases :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
lowerCases = cata go where
  go = \case
    anno C.:< CaseUPF x ls -> caseToNestedIfs anno x ls
    anno C.:< UnprocessedParsedTermH x -> anno :< UnprocessedParsedTermH x
    anno C.:< UnprocessedParsedTermL x -> anno :< UnprocessedParsedTermL x
    anno C.:< UnprocessedParsedTermB x -> anno :< UnprocessedParsedTermB x
    anno C.:< LetUPF bindings body     -> anno :< LetUPF bindings body
    anno C.:< ListUPF terms            -> anno :< ListUPF terms
    anno C.:< IntUPF n                 -> anno :< IntUPF n
    anno C.:< StringUPF s              -> anno :< StringUPF s

-- |A builtin function, given by its direct form once saturated. The
-- location is the one of the application that saturates it.
data Builtin
  = Unary (LocTag -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm)
  | Binary (LocTag -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm)

-- |The builtin functions, in binding order. 'addBuiltins' defines each as a
-- lambda over its direct form, and 'optimizeBuiltinFunctions' rewrites
-- applications of them to it.
builtins :: [(String, Builtin)]
builtins =
  [ ("left",  Unary  $ \a x -> a :< UnprocessedParsedTermH (HLeftF x))
  , ("right", Unary  $ \a x -> a :< UnprocessedParsedTermH (HRightF x))
  , ("trace", Unary  $ \a x -> a :< UnprocessedParsedTermH (HTraceF x))
  , ("abort", Unary  $ abortTerm UserAbort)
  , ("pair",  Binary $ \a x y -> a :< UnprocessedParsedTermB (PairSF x y))
  , ("app",   Binary $ \a x y -> a :< UnprocessedParsedTermL (AppF x y))
  ]

-- |Split an application into its head and its arguments, each argument
-- with the location of the application node that supplies it.
applicationSpine :: ExpandedSurfaceTerm -> (ExpandedSurfaceTerm, [(LocTag, ExpandedSurfaceTerm)])
applicationSpine = collect [] where
  collect args = \case
    a :< UnprocessedParsedTermL (AppF f x) -> collect ((a, x) : args) f
    h                                      -> (h, args)

-- |Apply a builtin to the arguments of a spine, giving its direct form and
-- the arguments left over, or a lambda awaiting the missing argument when
-- there are too few. Nothing when there are no arguments.
applyBuiltin :: Builtin -> [(LocTag, ExpandedSurfaceTerm)]
             -> Maybe (ExpandedSurfaceTerm, [(LocTag, ExpandedSurfaceTerm)])
applyBuiltin builtin args = case (builtin, args) of
  (_, [])                            -> Nothing
  (Unary f, (a, x) : rest)           -> Just (f a x, rest)
  (Binary f, (_, x) : (a, y) : rest) -> Just (f a x y, rest)
  (Binary f, [(a, x)])               -> Just (awaitArgument a (f a x), [])
  where
    argument = "__builtin_arg"
    awaitArgument a k = a :< UnprocessedParsedTermL
      (LamF (locatedName a argument) (k (a :< UnprocessedParsedTermL (VarF argument))))

-- |Rewrite applications of builtins that are in scope to their direct forms.
optimizeBuiltinFunctions :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
optimizeBuiltinFunctions = go (Set.fromList (fst <$> builtins))
  where
    go :: Set String -> ExpandedSurfaceTerm -> ExpandedSurfaceTerm
    go scope term@(anno :< t) = case t of
      UnprocessedParsedTermL (AppF _ _) ->
        let (h, args) = applicationSpine term
        in rewrite scope (go scope h) (second (go scope) <$> args)
      UnprocessedParsedTermL (LamF name body) ->
        anno :< UnprocessedParsedTermL (LamF name (go (Set.delete (locatedNameText name) scope) body))
      other -> anno :< mapScoped (go . foldr updateScope scope) other

    -- Arguments are already rewritten. The direct form of @app@ is itself an
    -- application, so its spine is rewritten in turn.
    rewrite :: Set String -> ExpandedSurfaceTerm -> [(LocTag, ExpandedSurfaceTerm)] -> ExpandedSurfaceTerm
    rewrite scope h args = case h of
      _ :< UnprocessedParsedTermL (VarF name)
        | name `Set.member` scope
        , Just builtin <- lookup name builtins
        , Just (direct, rest) <- applyBuiltin builtin args
        -> let (h', args') = applicationSpine direct
           in rewrite scope h' (args' <> rest)
      _ -> foldl (\f (a, x) -> a :< UnprocessedParsedTermL (AppF f x)) h args

    -- A let binder re-exposes a builtin when tagged as its definition;
    -- every other binder (including case-pattern variables, which the
    -- parser never tags 'BuiltinLoc') shadows it.
    updateScope name =
      let text = locatedNameText name
      in if locatedNameLoc name == BuiltinLoc text
           then Set.insert text
           else Set.delete text

-- |Bind @zero@, the 'builtins' and the 'caseHelpers' around the term.
addBuiltins :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
addBuiltins term = GeneratedLoc "addBuiltins" Nothing :< LetUPF bindings term
  where
    bindings = zero : (define <$> builtins) <> (helper <$> caseHelpers)
    zero = (locatedName (BuiltinLoc "zero") "zero", BuiltinLoc "zero" :< IntUPF 0)
    define (name, builtin) = (locatedName loc name, definition) where
      loc = BuiltinLoc name
      definition = case builtin of
        Unary f  -> lam loc "x" (f loc (var loc "x"))
        Binary f -> lam loc "x" (lam loc "y" (f loc (var loc "x") (var loc "y")))
    helper (name, definition) = (locatedName (GeneratedLoc "case helper" Nothing) name, definition)
