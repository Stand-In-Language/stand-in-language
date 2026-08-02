{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

-- |A small monadic DSL for constructing lowered terms while threading the
-- supply of function indexes and unsized-recursion tokens. Used by the
-- core lowering ('Telomare.Resolve.splitExpr') and by tests that
-- hand-assemble expected 'Term3' values.
module Telomare.IR.Builder where

import qualified Control.Comonad.Trans.Cofree as CofreeT (CofreeF (..))
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Functor.Foldable (Base, Corecursive (embed), Recursive (project))
import Telomare.IR.Base (BasicBase (..), BasicExprF (..), CarryAnno (..),
                         FunctionIndex, StuckBase (..), StuckF (..),
                         UnsizedRecursionToken, i2B, iteB_, pattern AbortB,
                         pattern EnvB, pattern LeftB, pattern PairP,
                         pattern RightB, pattern SetEnvB, pattern StuckEE,
                         pattern ZeroB, varB)
import Telomare.IR.Core (Term3, Term3F (..))
import Telomare.IR.Loc (LocTag)

type Term3Builder g = State (FunctionIndex, UnsizedRecursionToken) g

buildTerm :: (Corecursive g) => Term3Builder g -> g
buildTerm = flip State.evalState (toEnum 0, toEnum 0)

deferS :: (Base g ~ f, StuckBase f, Recursive g, Corecursive g) => g -> Term3Builder g
deferS x = do
  fi <- State.gets fst
  State.modify (\(_, urt) -> (succ fi, urt))
  pure . StuckEE $ DeferSF fi x

-- TODO: replace with PairP?
pairS :: (Base g ~ CofreeT.CofreeF f a, BasicBase f, Recursive g, Corecursive g, Monad m) => m g -> m g -> m g
pairS a b = do
  a' <- a
  b' <- b
  let l CofreeT.:< _ = project a'
  pure . embed $ l CofreeT.:< embedB (PairSF a' b')

clamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
clamS x = pairS (x >>= deferS) $ pure ZeroB

lamS :: forall g f. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g)
  => Term3Builder g -> Term3Builder g
lamS x = pairS (x >>= deferS) $ pure EnvB

twiddleS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g
twiddleS = deferS . PairP (LeftB $ RightB EnvB) . PairP (LeftB EnvB) $ RightB (RightB EnvB)

appS :: forall g f w. (Base g ~ CofreeT.CofreeF f LocTag, StuckBase f, BasicBase f, Recursive g, Corecursive g, CarryAnno g, CarryWrap g ~ w, BasicBase w)
  => Term3Builder g -> Term3Builder g -> Term3Builder g
appS c i = SetEnvB . SetEnvB <$> pairS twiddleS (pairS i c)

-- inside three lambdas (\r f x -> ...)
-- r is the repeater function
-- creates and iterates on a function "frame" (rf, (rf, (f', (x, env'))))
-- rf is the function to pull arguments out of the frame, run f', and construct the next frame
-- (f',env') is f (since f may contain a saved environment/closure env we want to use for each iteration)
repeatFunctionS :: LocTag -> Term3Builder Term3
repeatFunctionS l =
  let applyF = SetEnvB $ RightB EnvB
      env' = RightB . RightB $ RightB EnvB
      -- takes (rf, (f', (x, env'))), executes f' with (x, env') and creates a new frame
      rf = deferS $ PairP (LeftB EnvB)
                          (PairP (LeftB EnvB)
                                 (PairP (LeftB (RightB EnvB))
                                        (PairP applyF env')))
      r = LeftB . LeftB . RightB $ RightB EnvB
      x = LeftB EnvB
      f' = LeftB . LeftB $ RightB EnvB
      fenv = RightB . LeftB $ RightB EnvB
      -- (r, (x, ((f', fenv), 0))) -> (rf, (rf, (f', (x, fenv))))
      frameSetup = pairS rf (pairS rf (pure $ PairP f' (PairP x fenv)))
  in clamS . lamS . lamS $ SetEnvB <$> pairS (pure r) frameSetup

unsizedRepeater :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
unsizedRepeater l tok = clamS . pure . LeftB . RightB . RightB . RightB . embed $ l CofreeT.:< Term3Unsized tok

repeaterAndAbort :: LocTag -> UnsizedRecursionToken -> Term3Builder Term3
repeaterAndAbort l tok = pairS (unsizedRepeater l tok) abrt where
  -- args are (i, (b, ...)) since trb is on the stack
  -- abrt = (>>= deferS) $ SetEnvB . PairP (SetEnvB $ PairP AbortB abortToken) <$> appS (pure secondArgB) (pure firstArgB)
  abrt = (>>= deferS) $ SetEnvB . PairP (SetEnvB $ PairP AbortB abortToken) <$> appS (pure $ varB 1) (pure $ varB 0)
  abortToken = PairP ZeroB . i2B $ fromEnum tok

-- to construct a church numeral (\f x -> f ... (f x))
-- the core is nested setenvs around an env, where the number of setenvs is magnitude of church numeral
i2CB :: LocTag -> Int -> Term3Builder Term3
i2CB l n = appS (repeatFunctionS l) . clamS . pure . LeftB . RightB . RightB . RightB $ iterate SetEnvB EnvB !! n

-- function is called with (r,a), where r is the repeating function, and a is the abort function
unsizedRecursionWrapper :: LocTag -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3 -> Term3Builder Term3
unsizedRecursionWrapper loc t r b =
  let repeater = LeftB $ LeftB EnvB
      abrt = PairP (RightB $ LeftB EnvB) EnvB
      -- drop first arg (repeater)
      nsLamS :: Term3Builder Term3 -> Term3Builder Term3
      nsLamS x = pairS (x >>= deferS) (pure $ RightB EnvB)
      -- \t r b r' i -> if t i then r r' i else b i -- t r b are already on the stack when this is evaluated
      rWrap = nsLamS . lamS $ iteB_ <$> appS (pure $ varB 4) (pure $ varB 0)
                                    <*> appS (appS (pure $ varB 3) (pure $ varB 1)) (pure $ varB 0)
                                    <*> appS (pure $ varB 2) (pure $ varB 0)
      -- hack to make sure recursion test wrapper can be put in a definite place when sizing
      tWrap = pairS ((>>= deferS) (appS (pure $ varB 1) (pure $ varB 0))) (pairS t $ pure ZeroB)
      trb = pairS b . pairS r . pairS tWrap $ pure ZeroB
  in pairS (appS (appS (appS (repeatFunctionS loc) (pure repeater)) rWrap) (pure abrt) >>= deferS) trb
