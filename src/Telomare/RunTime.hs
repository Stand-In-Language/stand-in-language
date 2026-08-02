{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.RunTime where

import Control.Monad.IO.Class (MonadIO (..))
import PrettyPrint (prettyPrint)
import Telomare
import Telomare.Possible (basicStep, stuckStep, transformNoDefer)

showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= liftIO . print >> a

instance AbstractRunTime StuckExpr where
  eval = pure . transformNoDefer step where
    step = basicStep (stuckStep unhandledError)
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
