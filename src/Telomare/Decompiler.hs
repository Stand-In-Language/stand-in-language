{-# LANGUAGE LambdaCase #-}

module Telomare.Decompiler where

import Control.Comonad.Cofree (Cofree ((:<)))
import Control.Monad (foldM, liftM2)
import qualified Control.Monad.State as State
import Data.Functor.Foldable (embed, project)
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Semigroup (Max (..))
import Telomare

{-
decompileUPT :: UnprocessedParsedTerm -> String
decompileUPT =
  let lineLimit = 120
      -- "hello"
      showS :: String -> State.State Int String
      showS s = let indent = length s in State.modify (+ indent) >> pure s
      drawIndent = State.get >>= (\n -> pure $ replicate n ' ')
      drawList = fmap mconcat . sequence
      needsParens = \case -- will need parens if on right side of application
        AppUPF _ _ -> True
        LamUPF _ _ -> True
        LeftUPF _  -> True
        RightUPF _ -> True
        TraceUPF _ -> True
        LetUPF _ _ -> True
        ITEUPF {}  -> True
        _         -> False
      needsFirstParens = \case
        LamUPF _ _ -> True
        LetUPF _ _ -> True
        ITEUPF {}  -> True
        _         -> False
      drawParens x = if needsParens x
        then drawList [showS " (", draw $ embed x, showS ")"]
        else drawList [showS " ", draw $ embed x]
      drawFirstParens x = if needsFirstParens x
        then drawList [showS "(", draw $ embed x, showS ")"]
        else draw $ embed x
      draw :: UnprocessedParsedTerm -> State.State Int String
      draw = draw' . project
      draw' = \case
          VarUPF s -> showS s
          ITEUPF i t e -> drawList [showS "if ", draw i, showS " then ", draw t, showS " else ", draw e]
          LetUPF ((firstName, firstDef):bindingsXS) in_ -> if null bindingsXS
            then drawList [showS "let ", showS (locatedNameText firstName), showS " = ", draw firstDef, showS " in ", draw in_]
            else do
            startIn <- State.get
            l <- showS "let "
            startBind <- State.get
            fb <- drawList [showS (locatedNameText firstName), showS " = ", draw firstDef, pure "\n"]
            let drawOne (name, upt) = do
                  State.put startBind
                  drawList [drawIndent, showS (locatedNameText name), showS " = ", draw upt, pure "\n"]
            displayedBindings <- mconcat <$> traverse drawOne bindingsXS
            State.put startIn
            mconcat <$> sequence [pure l, pure fb, pure displayedBindings, drawIndent, showS "in ", draw in_]
          ListUPF l -> let insertCommas []     = []
                           insertCommas [x]    = [x]
                           insertCommas (x:xs) = x : showS "," : insertCommas xs
                       in drawList [showS "[", fmap concat . sequence . insertCommas $ fmap draw l, showS "]" ]
          IntUPF x -> showS $ show x
          StringUPF s -> drawList [showS "\"", showS s, showS "\""]
          PairUPF a b -> drawList [showS "(", draw a, showS ",", draw b, showS ")"]
          AppUPF f x -> drawList [drawFirstParens $ project f, drawParens $ project x]
          -- TODO flatten nested lambdas
          LamUPF n x -> drawList [showS "\\", showS (locatedNameText n), showS " -> ", draw x]
          ChurchUPF n -> drawList [showS "$", showS $ show n]
          UnsizedRecursionUPF t r b -> drawList [showS "{", draw t, showS ",", draw r, showS ",", draw b, showS "}"]
          LeftUPF x -> drawList [showS "left ", drawParens $ project x]
          RightUPF x -> drawList [showS "right ", drawParens $ project x]
          TraceUPF x -> drawList [showS "trace ", drawParens $ project x]
          CheckUPF c x -> drawList [draw x, showS " : ", draw c]

  in \x -> State.evalState (draw x) 0
-}
  {-
      safeTail s = if null s then [] else tail s
      showMem s = do
        let indent = length . last . takeWhile (not . null) . iterate (safeTail . dropWhile (/= '\n')) $ s
        if elem '\n' s
          then State.put indent
          else State.modify (+ indent)
        pure s
      draw oneLine =
        let showTwo a b = undefined --let long =
            showLine l = do
              indent <- State.get
              let long = intercalate " " l
                         in if length long > lineLimit
                            then

-}
              {-m
          drawLineOr x y = if not oneLine && draw
-}

{-
decompileTerm1 :: Term1 -> UnprocessedParsedTerm
decompileTerm1 = \case
  _ :< ParserTermB ZeroSF -> embed $ IntUPF 0
  _ :< ParserTermB (PairSF a b) -> embed $ PairUPF (decompileTerm1 a) (decompileTerm1 b)
  _ :< TVarF n -> embed $ VarUPF n
  _ :< TAppF f x -> AppUP (decompileTerm1 f) (decompileTerm1 x)
  _ :< TCheckF c x -> embed $ CheckUPF (decompileTerm1 c) (decompileTerm1 x)
  _ :< TITEF i t e ->ITEUP (decompileTerm1 i) (decompileTerm1 t) (decompileTerm1 e)
  _ :< TLeftF x -> embed $ LeftUPF (decompileTerm1 x)
  _ :< TRightF x -> embed $ RightUPF (decompileTerm1 x)
  _ :< TTraceF x -> embed $ TraceUPF (decompileTerm1 x)
  loc :< TLamF (Open n) x -> embed $ LamUPF (locatedName loc n) (decompileTerm1 x)
  loc :< TLamF (Closed n) x -> embed $ LamUPF (locatedName loc n) (decompileTerm1 x) -- not strictly equivalent
  _ :< TLimitedRecursionF t r b -> embed $ UnsizedRecursionUPF (decompileTerm1 t) (decompileTerm1 r) (decompileTerm1 b)
-}

decompileTerm2 :: Term2 -> Term1
decompileTerm2 =
  let nameSupply = (fmap (:[]) ['a'..'z'] <> ([x <> y | x <- nameSupply, y <- nameSupply]))
      getName n = if n < 0
        then head nameSupply
        else nameSupply !! n
      go :: Term2
         -> (Max Int, Term1)
      go = \case
        anno :< ParserTermB ZeroSF -> pure $ anno :< ParserTermB ZeroSF
        anno :< ParserTermB (PairSF a b) -> (\x y -> anno :< ParserTermB (PairSF x y)) <$> go a <*> go b
        anno :< TVarF n ->  (Max n, anno :< TVarF (getName n))
        anno :< TAppF f x -> (\y z -> anno :< TAppF y z) <$> go f <*> go x
        anno :< TCheckF c x -> (\y z -> anno :< TCheckF y z) <$> go c <*> go x
        anno :< TITEF i t e -> (\x y z -> anno :< TITEF x y z) <$> go i <*> go t <*> go e
        anno :< TLeftF x -> (anno :<) . TLeftF <$> go x
        anno :< TRightF x -> (anno :<) . TRightF <$> go x
        anno :< TTraceF x -> (anno :<) . TTraceF <$> go x
        anno :< TLamF (Open ()) x -> (\(Max n, r) -> (Max n, (anno :<) $ TLamF (Open (getName n)) r)) $ go x -- warning, untested
        anno :< TLamF (Closed ()) x -> (\(Max n, r) -> (Max 0, (anno :<) $ TLamF (Closed (getName n)) r)) $ go x
        anno :< TLimitedRecursionF t r b -> (\x y z -> anno :< TLimitedRecursionF x y z) <$> go t <*> go r <*> go b
  in snd . go
