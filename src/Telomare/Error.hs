{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE LambdaCase     #-}

-- |Every error the pipeline can produce, in one place. 'EvalError' unions
-- the per-stage errors ('ResolverError' from resolution, 'TypeCheckError'
-- from type checking, 'SizingFailure' from the sizing/totality pass,
-- 'RunTimeError' from evaluation) so drivers report one type.
module Telomare.Error where

import Control.DeepSeq (NFData (..))
import Data.Validity (Validity)
import GHC.Generics (Generic)
import Telomare.IR.Base (UnsizedRecursionToken (..))
import Telomare.IR.Core (RunTimeError)
import Telomare.IR.Loc (LocTag, renderLocTagCompact, renderLocTagVerbose)
import Telomare.IR.Types (PartialType)

data TypeCheckError
  = UnboundType Int
  | InconsistentTypes PartialType PartialType
  | RecursiveType Int
  deriving (Eq, Ord, Show)

data ResolverError
  = NoMainFunction String
  | ModuleNotFound String
  | DefinitionCycle [String]
  | MissingDefinitions [String]
  | MissingDefinitionAt LocTag String
  | ParseError String
  deriving (Eq, Ord)

instance Show ResolverError where
  showsPrec d err = showParen (d > 10) $ showString (renderResolverError err)

renderResolverError :: ResolverError -> String
renderResolverError = \case
  NoMainFunction moduleName -> "NoMainFunction " <> show moduleName
  ModuleNotFound moduleName -> "ModuleNotFound " <> show moduleName
  DefinitionCycle names -> "DefinitionCycle " <> show names
  MissingDefinitions names -> "MissingDefinitions " <> show names
  MissingDefinitionAt loc name ->
    "missing definition " <> show name <> " at " <> renderLocTagVerbose loc
  ParseError err -> "ParseError " <> show err

-- |Why the sizing pass could not pin a finite iteration count on a recursion
-- site. The two cases need different advice, so they are kept apart.
data SizingFailureKind
  = FuelExhausted Int
  -- ^The abstract unrolling reached this depth and the recursion's test still
  -- had not said "stop".
  | UnboundedInput
  -- ^The recursion's test reached input that no static refinement bounds, so
  -- no unrolling depth at all can be proven sufficient.
  deriving (Eq, Ord, Show, Generic, NFData)

instance Validity SizingFailureKind

-- |A sizing failure, named well enough to act on: which recursion, why, and
-- where it is in the source.
data SizingFailure = SizingFailure
  { sizingFailureToken :: UnsizedRecursionToken
  , sizingFailureKind  :: SizingFailureKind
  , sizingFailureLoc   :: Maybe LocTag
  }
  deriving (Eq, Ord, Show, Generic, NFData)

instance Validity SizingFailure

-- |Names the recursion site as precisely as the available information allows.
renderSizingSite :: SizingFailure -> String
renderSizingSite failure =
  let recursion = "recursion #" <> show (unUnsizedRecursionToken $ sizingFailureToken failure)
  in case sizingFailureLoc failure >>= renderLocTagCompact of
       Just place -> recursion <> " at " <> place
       Nothing    -> recursion

renderSizingFailure :: SizingFailure -> String
renderSizingFailure failure = case sizingFailureKind failure of
  FuelExhausted depth ->
    "could not size " <> renderSizingSite failure <> ":\n"
      <> "  its test had still not stopped after " <> show depth <> " unrollings.\n"
      <> "  Either it needs a deeper recursion than the sizing budget allows, or\n"
      <> "  its test never stops."
  UnboundedInput ->
    "could not size " <> renderSizingSite failure <> ":\n"
      <> "  its test depends on input that nothing bounds, so no finite iteration\n"
      <> "  count can be proven for it. Constrain that input with a refinement\n"
      <> "  (`x : someValidator`) or an `assert` before recursing on it."

data EvalError = RTE RunTimeError
    | TCE TypeCheckError
    | RE ResolverError
    | StaticCheckError String
    | CompileConversionError
    | RecursionLimitError SizingFailure
    deriving Eq

-- |As derived, except that a sizing failure shows the explanation rather than
-- its fields. Everything else keeps the shape callers already match on.
instance Show EvalError where
  showsPrec d = \case
    RTE err -> showParen (d > 10) $ showString "RTE " . showsPrec 11 err
    TCE err -> showParen (d > 10) $ showString "TCE " . showsPrec 11 err
    RE err -> showParen (d > 10) $ showString "RE " . showsPrec 11 err
    StaticCheckError s -> showParen (d > 10) $ showString "StaticCheckError " . showsPrec 11 s
    CompileConversionError -> showString "CompileConversionError"
    RecursionLimitError f -> showParen (d > 10) $ showString (renderSizingFailure f)

-- |What to show a user. Only a sizing failure reads differently from `show`:
-- it has advice worth giving unadorned.
renderEvalError :: EvalError -> String
renderEvalError = \case
  RecursionLimitError f -> renderSizingFailure f
  err                   -> show err
