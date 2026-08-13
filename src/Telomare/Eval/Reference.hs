{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- The 'AbstractRunTime' instances must live here rather than in
-- 'Telomare.IR.Core' (the class's home): their bodies are built from
-- 'Telomare.Machine' step algebras, and Machine imports IR.Core.
{-# OPTIONS_GHC -Wno-orphans #-}

-- |The reference evaluators: the 'AbstractRunTime' instances for
-- 'CompiledExpr' (the production path) and 'StuckExpr' (the REPL/test
-- path), the plain 'basicEval' interpreter, and the
-- barrier-based partial evaluator 'evalPartial'. All are assembled from
-- 'Telomare.Machine' step algebras.
--
-- 'Telomare.Eval.Meter' reimplements the 'CompiledExpr' instance with
-- step counting; the sizing tests assert the two agree.
module Telomare.Eval.Reference where

import Control.Applicative
import Data.Char (chr)
import Data.Functor.Foldable
import Telomare.IR.Base
import Telomare.IR.Core
import Telomare.Machine
import Telomare.PrettyPrint
import Telomare.PrettyPrint.Indent (indentWithTwoChildren')
import Telomare.Size.IR

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
    doLet letExpr = case cata lf letExpr of
      Just n -> pure [chr n]
      _      -> indentWithTwoChildren' "#/#" (pure "") (showP letExpr)
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
    StuckFW (DeferSF deferId x) -> deferB (fromEnum deferId) . cata removeBarriers $ transformNoDefer (step . addBarrier) x
    x -> handleOther x
  addBarrier = \case
    StuckFW EnvSF -> embedD $ BarrierF EnvB
    x -> x
  removeBarriers = \case
    DeferredFW (BarrierF x) -> x
    x -> seq x $ embed x -- does seq have any performance consequence here?
  wrapUnknownStep = deferredEE . BarrierF . embed


instance AbstractRunTime StuckExpr where
  eval = pure . transformNoDefer step where
    step = basicStep (stuckStep unhandledError)
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
