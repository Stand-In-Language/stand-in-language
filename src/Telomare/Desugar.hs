{-# LANGUAGE LambdaCase #-}

-- |Post-parse desugaring. Case expressions are lowered to nested if/else
-- chains by the type-changing 'desugarTerm' boundary,
-- builtin names are bound ('addBuiltins') and partially applied builtins
-- are rewritten to direct forms ('optimizeBuiltinFunctions').
--
-- Raw parse-level sugar (multi-pattern lambdas, list assignments, UDT
-- declarations) is expanded before this stage runs, by 'Telomare.Expand'.
module Telomare.Desugar where

import Control.Comonad.Cofree (Cofree (..))
import qualified Control.Comonad.Trans.Cofree as C
import Data.Bifunctor (first, second)
import Data.Function (on)
import Data.Functor.Foldable (Recursive (..))
import Data.List (nubBy)
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

-- |A path from the root of a matched term to one of its subterms: a
-- composition of 'HLeft' and 'HRight'.
type Path = DesugaredSurfaceTerm -> DesugaredSurfaceTerm

-- |The parts of a pattern that case lowering inspects.
data PatternNode
  = PairNode -- ^ The term must be a pair here
  | IntNode Int
  | StringNode String
  | VarNode LocatedName

-- |Every pair, literal and variable of a pattern, in left-to-right
-- preorder, with the path to it from the root.
-- e.g. PatternPair (PatternVar "x") (PatternPair (PatternInt 0) PatternIgnore)
--      will return [(id, PairNode), (HLeft, VarNode "x"), (HRight, PairNode), (HLeft . HRight, IntNode 0)]
patternNodes :: PatternA -> [(Path, PatternNode)]
patternNodes = cata alg where
  alg = \case
    PatternPairF x y      -> (id, PairNode) : (first (. HLeft) <$> x) <> (first (. HRight) <$> y)
    PatternIntF i         -> [(id, IntNode i)]
    PatternStringF str    -> [(id, StringNode str)]
    PatternVarF name      -> [(id, VarNode name)]
    PatternIgnoreF        -> []
    PatternAnnotatedF x _ -> x

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
caseToNestedIfs :: DesugaredSurfaceTerm -- ^ Term to be pattern matched
                -> [(PatternA, DesugaredSurfaceTerm)] -- ^ Alternatives
                -> DesugaredSurfaceTerm
caseToNestedIfs scrutinee@(anno :< _) alternatives = case scrutinee of
  VarP _ -> lower scrutinee
  _      -> AppP (LamP (locatedName generated scrutineeName)
                       (lower (generated :< UnprocessedParsedTermL (VarF scrutineeName))))
                 scrutinee
  where
    generated = GeneratedLoc "case scrutinee" (Just anno)
    scrutineeName = "__case_scrutinee"
    lower x = foldr (alternative x) nonExhaustive alternatives
    nonExhaustive =
      ITEP (anno :< IntUPF 1)
           (AppP (VarP "__case_abort") (anno :< StringUPF "Non-exhaustive patterns in case"))
           (anno :< IntUPF 0)
    -- An alternative without checks always matches, so later ones are dropped.
    alternative x (p, result@(resultAnno :< _)) next =
      let nodes = patternNodes p
          bound = bindPatternVars x nodes result
      in case matchChecks resultAnno x nodes of
        []     -> bound
        checks -> ITEP (allOf resultAnno checks) bound next

-- |Bool-valued checks that the term has the pattern's pair structure and
-- literals. Pair nodes are arbitrary values, so each is coerced to a Bool
-- before it reaches @and@, whose arguments are refined to Bool. Integers are
-- compared with @dEqual@ and strings, whole, with @listEqual@.
matchChecks :: LocTag -> DesugaredSurfaceTerm -> [(Path, PatternNode)] -> [DesugaredSurfaceTerm]
matchChecks anno x = concatMap check where
  check (path, node) = case node of
    PairNode       -> [ITEP (path x) (anno :< IntUPF 1) (anno :< IntUPF 0)]
    IntNode i      -> [equal "__case_dEqual" (path x) (anno :< IntUPF i)]
    StringNode str -> [equal "__case_listEqual" (path x) (anno :< StringUPF str)]
    VarNode _      -> []
  equal :: String -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
  equal helper a = AppP (AppP (VarP helper) a)

-- |The conjunction of non-empty Bool-valued checks.
allOf :: LocTag -> [DesugaredSurfaceTerm] -> DesugaredSurfaceTerm
allOf anno = \case
  [c]    -> c
  [a, b] -> AppP (AppP (rewriteOuterTag anno $ VarP "__case_and") a) b
  cs     -> AppP (AppP (AppP (rewriteOuterTag anno $ VarP "__case_foldl")
                             (VarP "__case_and"))
                       (anno :< IntUPF 1))
                 (anno :< ListUPF cs)

-- |Bind each pattern variable in the case result to its part of the term,
-- as an applied lambda. The leftmost occurrence of a repeated variable wins.
bindPatternVars :: DesugaredSurfaceTerm -> [(Path, PatternNode)] -> DesugaredSurfaceTerm
                -> DesugaredSurfaceTerm
bindPatternVars x nodes result = foldr bind result vars where
  vars = nubBy ((==) `on` (locatedNameText . fst)) [ (name, path x) | (path, VarNode name) <- nodes ]
  bind :: (LocatedName, DesugaredSurfaceTerm) -> DesugaredSurfaceTerm -> DesugaredSurfaceTerm
  bind (name, value) body = AppP (LamP name body) value

-- |Run every post-sugar rewrite and remove the case capability from the term
-- type before resolution.
desugarTerm :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
desugarTerm = lowerCases
            . optimizeBuiltinFunctions
            . addBuiltins
            . addCaseHelperAliases

lowerCases :: ExpandedSurfaceTerm -> DesugaredSurfaceTerm
lowerCases = cata go where
  go = \case
    _ C.:< CaseUPF x ls -> caseToNestedIfs x ls
    anno C.:< UnprocessedParsedTermH x -> anno :< UnprocessedParsedTermH x
    anno C.:< UnprocessedParsedTermL x -> anno :< UnprocessedParsedTermL x
    anno C.:< UnprocessedParsedTermB x -> anno :< UnprocessedParsedTermB x
    anno C.:< LetUPF bindings body     -> anno :< LetUPF bindings body
    anno C.:< ListUPF terms            -> anno :< ListUPF terms
    anno C.:< IntUPF n                 -> anno :< IntUPF n
    anno C.:< StringUPF s              -> anno :< StringUPF s

-- |Capture the helper definitions used by generated case code in the
-- outer resolved let. The aliases cannot be written in source, so nested
-- bindings cannot capture the generated references.
addCaseHelperAliases :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
addCaseHelperAliases _term@(loc :< LetUPF bindings body) =
  loc :< LetUPF (aliases <> bindings) body
  where
    aliases =
      [ ( locatedName (GeneratedLoc ("case helper " <> name) (Just loc)) alias
        , loc :< UnprocessedParsedTermL (VarF name)
        )
      | (name, alias) <- [ ("and", "__case_and")
                         , ("foldl", "__case_foldl")
                         , ("dEqual", "__case_dEqual")
                         , ("listEqual", "__case_listEqual")
                         , ("abort", "__case_abort")
                         ]
      , name `elem` (letBindingName <$> bindings)
      ]
addCaseHelperAliases term = term


rewriteOuterTag :: anno -> Cofree a anno -> Cofree a anno
rewriteOuterTag anno (_ :< x) = anno :< x


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

-- |Bind @zero@ and the 'builtins' around the term.
addBuiltins :: ExpandedSurfaceTerm -> ExpandedSurfaceTerm
addBuiltins term = GeneratedLoc "addBuiltins" Nothing :< LetUPF (zero : (define <$> builtins)) term
  where
    zero = (locatedName (BuiltinLoc "zero") "zero", BuiltinLoc "zero" :< IntUPF 0)
    define (name, builtin) = (locatedName loc name, definition) where
      loc = BuiltinLoc name
      var n = loc :< UnprocessedParsedTermL (VarF n)
      lam n body = loc :< UnprocessedParsedTermL (LamF (locatedName loc n) body)
      definition = case builtin of
        Unary f  -> lam "x" (f loc (var "x"))
        Binary f -> lam "x" (lam "y" (f loc (var "x") (var "y")))
