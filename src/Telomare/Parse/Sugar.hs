{-# LANGUAGE LambdaCase #-}

-- |In-parse desugaring. The grammar in 'Telomare.Parse' calls these while
-- constructing the surface AST, because the pre-desugared forms
-- (multi-pattern lambdas, list assignments, UDT declarations) have no
-- constructors in 'UnprocessedParsedTermF' to survive until a later pass.
-- Everything here is a pure @AUPT@ builder: no parser state is consumed, so
-- source spans and parse errors are exactly what the grammar alone produces.
--
-- Sugar that *is* representable in the surface AST ('CaseUPF', builtin
-- names) is expanded after parsing instead, in 'Telomare.Desugar'.
module Telomare.Parse.Sugar where

import Control.Comonad.Cofree (Cofree (..))
import Data.Bifunctor (first)
import Data.Char (isUpper)
import Data.Fix (Fix (..))
import Data.Functor (void)
import Data.Functor.Foldable (embed, project)
import Telomare.IR.Base
import Telomare.IR.Loc
import Telomare.IR.Surface

data AssignmentEntry
  = SingleAssignment LocatedName AUPT
  | ListAssignment LocTag [LocatedName] AUPT

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

-- |Build a single-argument lambda with optional destructuring.
-- Kept as a thin wrapper around 'buildMultiLambda' so existing callers
-- that work pattern-at-a-time continue to function.
makeLambda :: LocTag -> PatternA -> AUPT -> AUPT
makeLambda lt p = buildMultiLambda lt [(lt, p)]

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
