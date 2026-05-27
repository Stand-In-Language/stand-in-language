{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Telomare.RunTime where

-- import Control.Exception
import Control.Monad.Except
import Control.Monad.Fix
import Control.Monad.IO.Class (MonadIO (..))
import Data.Foldable
import Data.Functor.Foldable hiding (fold)
import Data.Functor.Identity
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import GHC.Exts (fromList)
import PrettyPrint (prettyPrint)
import System.IO (hGetContents)
import System.Process (CreateProcess (std_out), StdStream (CreatePipe),
                       createProcess, shell)
import Telomare
import Telomare.Possible (PPOut (..), basicStep, stuckStepDebug,
                          transformNoDefer)
import Text.Read (readMaybe)

debug :: Bool
debug = False

debugTrace :: String -> a -> a
debugTrace s x = if debug then trace s x else x

-- iEval' :: (IExpr -> IExpr -> Either RunTimeError IExpr) -> IExpr -> IExpr -> Either RunTimeError IExpr
-- iEval' f env g = let f' = f env in case g of
--   Trace -> pure $ trace (show env) env
--   Zero -> pure Zero
--   -- Abort -> pure Abort
--   Defer x -> pure $ Defer x
--   Pair a b -> Pair <$> f' a <*> f' b
--   Gate a b -> pure $ Gate a b
--   Env -> pure env
--   SetEnv x -> (f' x >>=) $ \case
--     Pair cf nenv -> case cf of
--       Defer c -> f nenv c
--       -- do we change env in evaluation of a/b, or leave it same? change seems more consistent, leave more convenient
--       Gate a b -> case nenv of
--         Zero -> f' a
--         _    -> f' b
--       z -> throwError $ SetEnvError z -- This should never actually occur, because it should be caught by typecheck
--     bx -> throwError $ SetEnvError bx -- This should never actually occur, because it should be caught by typecheck
--   PLeft g -> f' g >>= \case
--     (Pair a _) -> pure a
--     _          -> pure Zero
--   PRight g -> f' g >>= \case
--     (Pair _ x) -> pure x
--     _          -> pure Zero


-- |Evaluation with hvm backend
{-
hvmEval :: IExpr -> IO IExpr
hvmEval x = do
  (_, mhout, _, _) <- createProcess (shell ("hvm r ./hvm/backend \"(" <> show x <> ")\"")) { std_out = CreatePipe }
  case mhout of
    Just hout -> do
      hvmOutput <- hGetContents hout
      if (length . lines $ hvmOutput) > 2 then
        case (readMaybe . unlines . drop 2 . lines $ hvmOutput) :: Maybe IExpr of
          Just res -> pure res
          Nothing  -> error $ "Error: fail to read hvm output. \nhvm output:\n" <> hvmOutput
      else error $ "Error: hvm output is not what was expected. \nhvm output: " <> hvmOutput
      pure . read . unlines . drop 2 . lines $ hvmOutput
    Nothing -> error $ "Error: hvm failed to produce output. \nIExpr fed to hvm:\n" <> show x
-}

{- commenting out until fixed
llvmEval :: NExpr -> IO LLVM.RunResult
llvmEval nexpr = do
  let lmod = LLVM.makeModule nexpr
  when debug $ do
    print $ LLVM.DebugModule lmod
    putStrLn . concat . replicate 100 $ "                                                                     \n"
  result <- catch (LLVM.evalJIT LLVM.defaultJITConfig lmod) $ \(e :: SomeException) -> pure . Left $ show e
  case result of
    Left s -> do
      hPrint stderr nexpr
      hPutStrLn stderr $ "failed llvmEval: " ++ s
      fail s
    Right x -> pure x
-}

showPass :: (Show a, MonadIO m) => m a -> m a
showPass a = a >>= liftIO . print >> a

instance AbstractRunTime StuckExpr where
  eval = pure . transformNoDefer step where
    step = basicStep (stuckStepDebug unhandledError)
    unhandledError x = error $ "CompiledExpr eval unhandled case " <> prettyPrint x
