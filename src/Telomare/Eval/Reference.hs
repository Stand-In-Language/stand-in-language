{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- |The reference evaluators: the 'AbstractRunTime' instances for
-- 'CompiledExpr' (the production path) and 'StuckExpr' (the REPL/test
-- path), the plain 'basicEval'/'regularEval' interpreters, and the
-- barrier-based partial evaluator 'evalPartial'. All are assembled from
-- 'Telomare.Machine' step algebras.
--
-- 'Telomare.Eval.Meter' reimplements the 'CompiledExpr' instance with
-- step counting; the sizing tests assert the two agree.
module Telomare.Eval.Reference where

import Control.Applicative
import Control.Comonad.Cofree (Cofree ((:<)), hoistCofree)
import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Lens.Plated (transform)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader (Reader, ReaderT, ask, local, runReaderT)
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.State.Lazy as StateL
import Control.Monad.State.Strict (State, StateT)
import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class
import Data.Bifunctor
import Data.Char (chr)
import Data.Fix (Fix (..), hoistFix')
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Foldable.TH
import Data.Kind
import Data.List (nub, nubBy, partition, sortBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
-- import Data.SBV ((.<), (.>))
import Control.Comonad.Trans.Cofree (CofreeF, headF)
import Control.Exception (Exception)
import Control.Exception.Base (throw)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Reader.Class
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Semigroup (Max (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Debug.Trace
import GHC.Generics (Generic)
import Telomare.Error
import Telomare.IR.Base
import Telomare.IR.Builder
import Telomare.IR.Core
import Telomare.IR.Loc
import Telomare.IR.Surface
import Telomare.IR.Types
import Telomare.Machine
import Telomare.PrettyPrint
import Telomare.PrettyPrint.Indent (indentWithChildren', indentWithOneChild,
                                    indentWithOneChild', indentWithTwoChildren,
                                    indentWithTwoChildren', sindent)
import Telomare.Size.IR

regularEval :: forall f g. (Base g ~ f, BasicBase f, StuckBase f, AbortBase f, IndexedInputBase f, UnsizedBase f
               , Recursive g, Corecursive g, PrettyPrintable g) => g -> g
regularEval = transformNoDefer f . cata ss where
  f = basicStep (stuckStep (abortStep (indexedInputStep Set.empty unhandledError)))
  unhandledError z = error ("regularEval unhandled case\n" <> prettyPrint (embed z))
  ss :: f g -> g
  ss = \case
    UnsizedFW (RefinementWrapperF lt tc c) ->
      let innerTC = appB (LeftB EnvB) (RightB EnvB)
          performTC = deferB removeRefinementWrappersTC . SetEnvB $ PairB (SetEnvB $ PairB (AbortEE AbortF) innerTC) (RightB EnvB)
      in SetEnvB $ PairB performTC (PairB tc c)
    UnsizedFW (UnsizedStubF _ _) -> iterate SetEnvB EnvB !! 255
    x -> embed x

basicEval :: forall f g. (Base g ~ f, BasicBase f, StuckBase f, Recursive g, Corecursive g, PrettyPrintable g) => g -> g
basicEval = transformNoDefer f where
  f = basicStep (stuckStep unhandledError)
  unhandledError z = error ("basicEval unhandled case:\n" <> prettyPrint (embed z))

newtype PPOut a = PPOut a
--   deriving Functor

instance {-# OVERLAPPING #-} PrettyPrintable (PPOut CompiledExpr) where
  showP (PPOut x) = f x where
    f = \case
      BasicEE ZeroSF -> pure ""
      BasicEE (PairSF a b) -> liftA2 (<>) (doLet a) (f b)
      z -> indentWithTwoChildren' "#!#" (pure "") (showP z)
    doLet x = case cata lf x of
      Just n -> pure [chr n]
      _      -> indentWithTwoChildren' "#/#" (pure "") (showP x)
    lf = \case
      BasicFW ZeroSF -> Just 0
      BasicFW (PairSF n (Just 0)) -> succ <$> n
      _ -> Nothing

instance AbstractRunTime CompiledExpr where
  eval = checkError . (\x -> debugTrace ("CompiledExpr eval " <> dumpEval x) x) . transformNoDefer step where
    dumpEval = \case
      BasicEE (PairSF o s) -> "output:\n" <> prettyPrint (PPOut o) <> "\nnew state:\n" <> prettyPrint s
      z -> "unexpected eval state:\n" <> prettyPrint z
    step = basicStep (stuckStep (abortStep unhandledError))
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
    findError = \case
      AbortFW (AbortedF e) -> Just e
      x -> asum x
    checkError x = case cata findError x of
      Just e -> Left $ AbortRunTime e
      _      -> pure x

evalPartial :: (Base g ~ f, Traversable f, BasicBase f, StuckBase f, DeferredEvalBase f, Recursive g, Corecursive g, PrettyPrintable g)
  => g -> g
evalPartial = cata removeBarriers . transformNoDefer step where
  step = deferStep (basicStep (stuckStep (deferredEvalStep' wrapUnknownStep)))
  deferStep handleOther = \case
    StuckFW (DeferSF id x) -> deferB (fromEnum id) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    StuckFW EnvSF -> embedD $ BarrierF EnvB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> seq x $ embed x -- does seq have any performance consequence here?
  wrapUnknownStep = deferredEE . BarrierF . embed


showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= liftIO . print >> a

instance AbstractRunTime StuckExpr where
  eval = pure . transformNoDefer step where
    step = basicStep (stuckStep unhandledError)
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
