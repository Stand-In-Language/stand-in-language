module Main where

import Control.Applicative (liftA2)
import Debug.Trace
import Data.Char
import Data.List (partition)
import Data.Monoid
import SIL
import SIL.Eval
import SIL.Parser
import SIL.RunTime
import SIL.TypeChecker
import SIL.Optimizer
import SIL.Serializer
import System.Exit
import System.IO
import Test.Hspec
import Test.QuickCheck
import qualified System.IO.Strict as Strict

-- Common datatypes for generating SIL AST.
import Common

-- recursively finds shrink matching invariant, ordered simplest to most complex
shrinkComplexCase :: Arbitrary a => (a -> Bool) -> [a] -> [a]
shrinkComplexCase test a =
  let shrinksWithNextLevel = map (\x -> (x, filter test $ shrink x)) a
      (recurseable, nonRecursable) = partition (not . null . snd) shrinksWithNextLevel
  in shrinkComplexCase test (concat $ map snd recurseable) ++ map fst nonRecursable

three_succ = app (app (toChurch 3) (lam (pair (varN 0) zero))) zero

one_succ = app (app (toChurch 1) (lam (pair (varN 0) zero))) zero

two_succ = app (app (toChurch 2) (lam (pair (varN 0) zero))) zero

church_type = pair (pair zero zero) (pair zero zero)

c2d = lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)

h2c i =
  let layer recurf i churchf churchbase =
        if i > 0
        then churchf $ recurf (i - 1) churchf churchbase
        -- app v1 (app (app (app v3 (pleft v2)) v1) v0)
        else churchbase
      stopf i churchf churchbase = churchbase
  in \cf cb -> layer (layer (layer (layer stopf))) i cf cb


{-
h_zipWith a b f =
  let layer recurf zipf a b =
        if a > 0
        then if b > 0
             then pair (zipf (pleft a) (pleft b)) (recurf zipf (pright a) (pright b))
             else zero
        else zero
      stopf _ _ _ = zero
  in layer (layer (layer (layer stopf))) a b f

foldr_h =
  let layer recurf f accum l =
        if not $ nil l
        then recurf f (f (pleft l) accum) (pright l)
        else accum
-}

test_toChurch = app (app (toChurch 2) (lam (pair (varN 0) zero))) zero

map_ =
  -- layer recurf f l = pair (f (pleft l)) (recurf f (pright l))
  let layer = lam (lam (lam
                            (ite (varN 0)
                            (pair
                             (app (varN 1) (pleft $ varN 0))
                             (app (app (varN 2) (varN 1))
                              (pright $ varN 0)))
                            zero
                            )))
      base = lam (lam (pleft (pair zero var)))
  in app (app (toChurch 255) layer) base

foldr_ =
  let layer = lam (lam (lam (lam
                                 (ite (varN 0)
                                 (app (app (app (varN 3) (varN 2))

                                       (app (app (varN 2) (pleft $ varN 0))
                                            (varN 1)))
                                  (pright $ varN 0))
                                 (varN 1)
                                 )
                                 )))
      base = lam (lam (lam zero)) -- var 0?
  in app (app (toChurch 255) layer) base

zipWith_ =
  let layer = lam (lam (lam (lam
                                  (ite (varN 1)
                                   (ite (varN 0)
                                    (pair
                                     (app (app (varN 2) (pleft $ varN 1))
                                      (pleft $ varN 0))
                                     (app (app (app (varN 3) (varN 2))
                                           (pright $ varN 1))
                                      (pright $ varN 0))
                                    )
                                    zero)
                                   zero)
                                 )))
      base = lam (lam (lam zero))
  in app (app (toChurch 255) layer) base

-- layer recurf i churchf churchbase
-- layer :: (zero -> baseType) -> zero -> (baseType -> baseType) -> baseType
--           -> baseType
-- converts plain data type number (0-255) to church numeral
d2c baseType =
  let layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (app (varN 1)
                              (app (app (app (varN 3)
                                   (pleft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
  in app (app (toChurch 255) layer) base

-- d_equality_h iexpr = (\d -> if d > 0
--                                then \x -> d_equals_one ((d2c (pleft d) pleft) x)
--                                else \x -> if x == 0 then 1 else 0
--                         )
--

d_equals_one = lam (ite (varN 0) (ite (pleft (varN 0)) zero (i2g 1)) zero)

d_to_equality = lam (lam (ite (varN 1)
                                          (app d_equals_one (app (app (app (d2c zero) (pleft $ varN 1)) (lam . pleft $ varN 0)) (varN 0)))
                                          (ite (varN 0) zero (i2g 1))
                                         ))

list_equality =
  let pairs_equal = app (app (app zipWith_ d_to_equality) (varN 0)) (varN 1)
      length_equal = app (app d_to_equality (app list_length (varN 1)))
                     (app list_length (varN 0))
      and_ = lam (lam (ite (varN 1) (varN 0) zero))
      folded = app (app (app foldr_ and_) (i2g 1)) (pair length_equal pairs_equal)
  in lam (lam folded)

list_length = lam (app (app (app foldr_ (lam (lam (pair (varN 0) zero))))
                                  zero)
  (varN 0))

plus_ x y =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app (app plus x) y

d_plus = lam (lam (app c2d (plus_
                                   (app (d2c zero) (varN 1))
                                   (app (d2c zero) (varN 0))
                                   )))

d2c_test =
  let s_d2c = app (app (toChurch 3) layer) base
      layer = lam (lam (lam (lam (ite
                             (varN 2)
                             (app (varN 1)
                              (app (app (app (varN 3)
                                   (pleft $ varN 2))
                                   (varN 1))
                                   (varN 0)
                                  ))
                             (varN 0)
                            ))))
      base = lam (lam (lam (varN 0)))
  in app (app (app s_d2c (i2g 2)) (lam (pair (varN 0) zero))) zero

d2c2_test = ite zero (pleft (i2g 1)) (pleft (i2g 2))

c2d_test = app c2d (toChurch 2)
c2d_test2 = app (lam (app (app (varN 0) (lam (pair (varN 0) zero))) zero)) (toChurch 2)
c2d_test3 = app (lam (app (varN 0) zero)) (lam (pair (varN 0) zero))

double_app = app (app (lam (lam (pair (varN 0) (varN 1)))) zero) zero

test_plus0 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) zero))
test_plus1 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 1)))
test_plus254 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 254)))
test_plus255 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 255)))
test_plus256 = app c2d (plus_
                         (toChurch 3)
                         (app (d2c zero) (i2g 256)))

one_plus_one =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app c2d (app (app plus (toChurch 1)) (toChurch 1))

-- m f (n f x)
-- app (app m f) (app (app n f) x)
-- app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
three_plus_two =
  let succ = lam (pair (varN 0) zero)
      plus_app = app (app (varN 3) (varN 1)) (app (app (varN 2) (varN 1)) (varN 0))
      plus = lam (lam (lam (lam plus_app)))
  in app c2d (app (app plus (toChurch 3)) (toChurch 2))

-- (m (n f)) x
-- app (app m (app n f)) x
three_times_two =
  let succ = lam (pair (varN 0) zero)
      times_app = app (app (varN 3) (app (varN 2) (varN 1))) (varN 0)
      times = lam (lam (lam (lam times_app)))
  in app (app (app (app times (toChurch 3)) (toChurch 2)) succ) zero

-- m n
-- app (app (app (m n)) f) x
three_pow_two =
  let succ = lam (pair (varN 0) zero)
      pow_app = app (app (app (varN 3) (varN 2)) (varN 1)) (varN 0)
      pow = lam (lam (lam (lam pow_app)))
  in app (app (app (app pow (toChurch 2)) (toChurch 3)) succ) zero

-- unbound type errors should be allowed for purposes of testing runtime
allowedTypeCheck :: Maybe TypeCheckError -> Bool
allowedTypeCheck Nothing = True
allowedTypeCheck (Just (UnboundType _)) = True
allowedTypeCheck _ = False

testEval :: IExpr -> IO IExpr
testEval iexpr = optimizedEval (SetEnv (Pair (Defer deserialized) Zero))
    where serialized   = serialize iexpr
          deserialized = unsafeDeserialize serialized

unitTest :: String -> String -> IExpr -> Spec
unitTest name expected iexpr = it name $ if allowedTypeCheck (typeCheck ZeroType iexpr)
  then do
    result <- (show . PrettyIExpr) <$> testEval iexpr
    result `shouldBe` expected
  else expectationFailure ( concat [name, " failed typecheck: ", show (typeCheck ZeroType iexpr)])

unitTestRefinement :: String -> Bool -> IExpr -> Spec
unitTestRefinement name shouldSucceed iexpr = it name $ case inferType iexpr of
  Right t -> case (pureEvalWithError iexpr, shouldSucceed) of
    (Left err, True) -> do
      expectationFailure $ concat [name, ": failed refinement type -- ", show err]
    (Right _, False) -> do
      expectationFailure $ concat [name, ": expected refinement failure, but passed"]
    _ -> pure ()
  Left err -> do
    expectationFailure $ concat ["refinement test failed typecheck: ", name, " ", show err]
{-
unitTestOptimization :: String -> IExpr -> IO Bool
unitTestOptimization name iexpr = if optimize iexpr == optimize2 iexpr
  then pure True
  else (putStrLn $ concat [name, ": optimized1 ", show $ optimize iexpr, " optimized2 "
                          , show $ optimize2 iexpr])
  >> pure False
-}

churchType = (ArrType (ArrType ZeroType ZeroType) (ArrType ZeroType ZeroType))

rEvaluationIsomorphicToIEvaluation :: ZeroTypedTestIExpr -> Bool
rEvaluationIsomorphicToIEvaluation vte = case (pureEval $ getIExpr vte, pureREval $ getIExpr vte) of
  {-
  (Left _, Left _) -> True
  -- (Right a, Right b) -> a == b
  (Right _, Right _) -> True
  (Left _, Right _) -> True -- I guess failing to fail is fine for rEval
-}
  (Left _, Left _) -> True
  (a, b) | a == b -> True
  _ -> False

debugREITIE :: IExpr -> IO Bool
debugREITIE iexpr = if pureEval iexpr == pureREval iexpr
  then pure True
  else do
  putStrLn . concat $ ["ieval: ", show $ pureEval iexpr]
  putStrLn . concat $ ["reval: ", show $ pureREval iexpr]
  pure False

partiallyEvaluatedIsIsomorphicToOriginal:: ArrowTypedTestIExpr -> Bool
--partiallyEvaluatedIsIsomorphicToOriginal vte = pureREval (app (getIExpr vte) 0) == pureREval (app ())
partiallyEvaluatedIsIsomorphicToOriginal vte =
  let iexpr = getIExpr vte
      sameError (GenericRunTimeError sa _) (GenericRunTimeError sb _) = sa == sb
      -- sameError (SetEnvError _) (SetEnvError _) = True
      sameError a b = a == b
  in case (\x -> pureREval (app x Zero)) <$> eval iexpr of
  Left (RTE e) -> Left e == pureREval (app iexpr Zero)
  Right x -> case (x, pureREval (app iexpr Zero)) of
    (Left a, Left b) -> sameError a b
    (a, b) -> a == b

debugPEIITO :: IExpr -> Expectation
debugPEIITO iexpr = do
  putStrLn "regular app:"
  putStrLn $ show (app iexpr Zero)
  putStrLn "r-optimized:"
  showROptimized $ app iexpr Zero
  putStrLn "evaled:"
  putStrLn $ show (eval iexpr)
  case (\x -> pureREval (app x Zero)) <$> eval iexpr of
    Left (RTE e) ->
      expectationFailure
        (unlines
           [ concat $ ["partially evaluated error: ", show e]
           , concat $ ["regular evaluation result: ", show (pureREval (app iexpr Zero))]])
    Right x ->
      expectationFailure
        (unlines
           [ concat $ ["partially evaluated result: ", show x]
           , concat $ ["normally evaluated result: ", show (pureREval (app iexpr Zero))]])

unitTests_ :: Spec
unitTests_ = do
  unitTest "basiczero" "0" Zero
  unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
  unitTest "c2d" "2" c2d_test
  unitTest "c2d2" "2" c2d_test2
  unitTest "c2d3" "1" c2d_test3
  unitTest "oneplusone" "2" one_plus_one
  unitTest "abort" "1" (pair (Abort (pair zero zero)) zero)
  unitTest "notAbort" "2" (pair (pair (Abort zero) zero) zero)

isInconsistentType (Just (InconsistentTypes _ _)) = True
isInconsistentType _ = False

isRecursiveType (Just (RecursiveType _)) = True
isRecursiveType _ = False

unitTestTypeP :: IExpr -> Either TypeCheckError PartialType -> IO Bool
unitTestTypeP iexpr expected = if inferType iexpr == expected
  then pure True
  else do
  putStrLn $ concat ["type inference error ", show iexpr, " expected ", show expected
                    , " result ", show (inferType iexpr)
                    ]
  pure False

unitTestQC :: Testable p => String -> Int -> p -> IO Bool
unitTestQC name times p = quickCheckWithResult stdArgs { maxSuccess = times } p >>= \result -> case result of
  (Success _ _ _) -> pure True
  x -> (putStrLn $ concat [name, " failed: ", show x]) >> pure False

debugMark s = hPutStrLn stderr s >> pure True

unitTests :: (String -> String -> Spec) -> (String -> DataType -> (Maybe TypeCheckError -> Bool) -> Spec) -> Spec
unitTests unitTest2 unitTestType = do
  describe "type checker" $ do
    unitTestType "main = \\x -> {x,0}" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
    unitTestType "main = \\x -> {x,0}" ZeroType isInconsistentType
    unitTestType "main = succ 0" ZeroType (== Nothing)
    unitTestType "main = succ 0" (ArrType ZeroType ZeroType) isInconsistentType
    unitTestType "main = or 0" (PairType (ArrType ZeroType ZeroType) ZeroType) (== Nothing)
    unitTestType "main = or 0" ZeroType isInconsistentType
    unitTestType "main = or succ" (ArrType ZeroType ZeroType) isInconsistentType
    unitTestType "main = 0 succ" ZeroType isInconsistentType
    unitTestType "main = 0 0" ZeroType isInconsistentType
    -- I guess this is inconsistently typed now?
    unitTestType "main = \\f -> (\\x -> f (x x)) (\\x -> f (x x))"
      (ArrType (ArrType ZeroType ZeroType) ZeroType) (/= Nothing) -- isRecursiveType
    unitTestType "main = (\\f -> f 0) (\\g -> {g,0})" ZeroType (== Nothing)
    unitTestType "main : (#x -> if x then \"fail\" else 0) = 0" ZeroType (== Nothing)
  -- TODO fix
  --, unitTestType "main : (\\x -> if x then \"fail\" else 0) = 1" ZeroType isRefinementFailure
  describe "unitTest" $ do
    unitTest "ite" "2" (ite (i2g 1) (i2g 2) (i2g 3))
    unitTest "abort" "1" (pair (Abort (pair zero zero)) zero)
    unitTest "notAbort" "2" (pair (pair (Abort zero) zero) zero)
    unitTest "c2d" "2" c2d_test
    unitTest "c2d2" "2" c2d_test2
    unitTest "c2d3" "1" c2d_test3
    unitTest "oneplusone" "2" one_plus_one
    unitTest "church 3+2" "5" three_plus_two
    unitTest "3*2" "6" three_times_two
    unitTest "3^2" "9" three_pow_two
    unitTest "test_tochurch" "2" test_toChurch
    unitTest "three" "3" three_succ
    unitTest "data 3+5" "8" $ app (app d_plus (i2g 3)) (i2g 5)
    unitTest "foldr" "13" $ app (app (app foldr_ d_plus) (i2g 1)) (ints2g [2,4,6])
    unitTest "listlength0" "0" $ app list_length zero
    unitTest "listlength3" "3" $ app list_length (ints2g [1,2,3])
    unitTest "zipwith" "{{4,1},{{5,1},{{6,2},0}}}"
      $ app (app (app zipWith_ (lam (lam (pair (varN 1) (varN 0)))))
                 (ints2g [4,5,6]))
            (ints2g [1,1,2,3])
    unitTest "listequal1" "1" $ app (app list_equality (s2g "hey")) (s2g "hey")
    unitTest "listequal0" "0" $ app (app list_equality (s2g "hey")) (s2g "he")
    unitTest "listequal00" "0" $ app (app list_equality (s2g "hey")) (s2g "hel")
  -- because of the way lists are represented, the last number will be prettyPrinted + 1
    unitTest "map" "{2,{3,5}}" $ app (app map_ (lam (pair (varN 0) zero)))
                                     (ints2g [1,2,3])
  describe "refinement" $ do
    unitTestRefinement "minimal refinement success" True (check zero (completeLam (varN 0)))
    unitTestRefinement "minimal refinement failure" False
      (check (i2g 1) (completeLam (ite (varN 0) (s2g "whoops") zero)))
    unitTestRefinement "refinement: test of function success" True
     (check (lam (pleft (varN 0))) (completeLam (app (varN 0) (i2g 1))))
    unitTestRefinement "refinement: test of function failure" False
     (check (lam (pleft (varN 0))) (completeLam (app (varN 0) (i2g 2))))
  describe "unitTest2" $ do
    unitTest2 "main = 0" "0"
    unitTest2 fiveApp "5"
    unitTest2 "main = plus $3 $2 succ 0" "5"
    unitTest2 "main = times $3 $2 succ 0" "6"
    unitTest2 "main = pow $3 $2 succ 0" "8"
    unitTest2 "main = plus (d2c 5) (d2c 4) succ 0" "9"
    unitTest2 "main = foldr (\\a b -> plus (d2c a) (d2c b) succ 0) 1 [2,4,6]" "13"
    unitTest2 "main = dEqual 0 0" "1"
    unitTest2 "main = dEqual 1 0" "0"
    unitTest2 "main = dEqual 0 1" "0"
    unitTest2 "main = dEqual 1 1" "1"
    unitTest2 "main = dEqual 2 1" "0"
    unitTest2 "main = dEqual 1 2" "0"
    unitTest2 "main = dEqual 2 2" "1"
    unitTest2 "main = listLength []" "0"
    unitTest2 "main = listLength [1,2,3]" "3"
    unitTest2 "main = listEqual \"hey\" \"hey\"" "1"
    unitTest2 "main = listEqual \"hey\" \"he\"" "0"
    unitTest2 "main = listEqual \"hey\" \"hel\"" "0"
    unitTest2 "main = listPlus [1,2] [3,4]" "{1,{2,{3,5}}}"
    unitTest2 "main = listPlus 0 [1]" "2"
    unitTest2 "main = listPlus [1] 0" "2"
    unitTest2 "main = concat [\"a\",\"b\",\"c\"]" "{97,{98,100}}"
    unitTest2 nestedNamedFunctionsIssue "2"
    unitTest2 "main = take $0 [1,2,3]" "0"
    unitTest2 "main = take $1 [1,2,3]" "2"
    unitTest2 "main = take $5 [1,2,3]" "{1,{2,4}}"
    unitTest2 "main = c2d (minus $4 $3)" "1"
    unitTest2 "main = c2d (minus $4 $4)" "0"
    unitTest2 "main = dMinus 4 3" "1"
    unitTest2 "main = dMinus 4 4" "0"
    unitTest2 "main = (if 0 then (\\x -> {x,0}) else (\\x -> {{x,0},0})) 1" "3"
    unitTest2 "main = range 2 5" "{2,{3,5}}"
    unitTest2 "main = range 6 6" "0"
    unitTest2 "main = c2d (factorial 4)" "24"
    unitTest2 "main = c2d (factorial 0)" "1"
    unitTest2 "main = filter (\\x -> dMinus x 3) (range 1 8)"
      "{4,{5,{6,8}}}"
    unitTest2 "main = quicksort [4,3,7,1,2,4,6,9,8,5,7]"
      "{1,{2,{3,{4,{4,{5,{6,{7,{7,{8,10}}}}}}}}}}"
  -- , debugPEIITO (SetEnv (Twiddle (Twiddle (Pair (Defer Var) Zero))))
  -- , debugPEIITO (SetEnv (Pair (Defer Var) Zero))
  -- , debugPEIITO (SetEnv (Pair (Defer (Pair Zero Var)) Zero))
  -- , debugREITIE (SetEnv (Pair Env Env))
  -- , debugREITIE (Defer (SetEnv (Pair (Gate Env) (Pair Env Env))))
  -- , debugREITIE (SetEnv (Twiddle (Pair Env Env)))
  -- , debugREITIE (SetEnv (Pair (Gate (SetEnv (Pair (PRight Env) Env))) (Pair Env (Twiddle (PLeft Env)))))

  {-
  , Debugpcpt $ gate (check zero var)
  , debugPCPT $ app var (check zero var)
  , unitTestQC "promotingChecksPreservesType" promotingChecksPreservesType_prop
  , unitTestOptimization "listequal0" $ app (app list_equality (s2g "hey")) (s2g "he")
  , unitTestOptimization "map" $ app (app map_ (lam (pair (varN 0) zero))) (ints2g [1,2,3])
  -}
  -- ++ quickCheckTests unitTest2 unitTestType

-- slow, don't regularly run
quickCheckTests unitTest2 unitTestType =
  [ unitTestQC "rEvaluationIsIsomorphicToIEvaluation" 100 rEvaluationIsomorphicToIEvaluation
  -- too slow
  -- , unitTestQC "partiallyEvaluatedIsIsomorphicToOriginal" 100 partiallyEvaluatedIsIsomorphicToOriginal
  ]

testExpr = concat
  [ "main = let a = 0\n"
  , "           b = 1\n"
  , "       in {a,1}\n"
  ]

fiveApp = concat
  [ "main = let fiveApp = $5\n"
  , "       in fiveApp (\\x -> {x,0}) 0"
  ]

nestedNamedFunctionsIssue = concat
  [ "main = let bindTest = \\tlb -> let f1 = \\f -> f tlb\n"
  , "                                   f2 = \\f -> succ (f1 f)\n"
  , "                               in f2 succ\n"
  , "       in bindTest 0"
  ]

main = do
  preludeFile <- Strict.readFile "Prelude.sil"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ show pe
    unitTestP s g = case parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", show e]
      Right pg -> if pg == g
        then pure ()
        else putStrLn $ concat ["parsed oddly ", s, " ", show pg, " compared to ", show g]
    unitTest2 s r = it s $ case parseMain prelude s of
      Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
      Right g -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
        then pure ()
        else expectationFailure $ concat [s, " result ", r2]
    unitTest3 s r = let parsed = parseMain prelude s in case (inferType <$> parsed, parsed) of
      (Right (Right _), Right g) -> fmap (show . PrettyIExpr) (testEval g) >>= \r2 -> if r2 == r
        then pure True
        else (putStrLn $ concat [s, " result ", r2]) >> pure False
      e -> (putStrLn $ concat ["failed unittest3: ", s, " ", show e ]) >> pure False
    unitTest4 s t = let parsed = parseMain prelude s in case debugInferType <$> parsed of
      (Right (Right it)) -> if t == it
        then pure True
        else do
        putStrLn $ concat ["expected type ", show t, " inferred type ", show it]
        pure False
      e -> do
        putStrLn $ concat ["could not infer type ", show e]
        pure False
    unitTestType s t tef = it s $ case parseMain prelude s of
      Left e -> expectationFailure $ concat ["failed to parse ", s, " ", show e]
      Right g -> let apt = typeCheck t g
                 in if tef apt
                    then pure ()
                    else expectationFailure $
                          concat [s, " failed typecheck, result ", show apt]
    parseSIL s = case parseMain prelude s of
      Left e -> concat ["failed to parse ", s, " ", show e]
      Right g -> show g

  -- TODO change eval to use rEval, then run this over a long non-work period
  {-
  let isProblem (TestIExpr iexpr) = typeable (TestIExpr iexpr) && case eval iexpr of
        Left _ -> True
        _ -> False
  (Right mainAST) <- parseMain prelude <$> Strict.readFile "tictactoe.sil"
  print . head $ shrinkComplexCase isProblem [TestIExpr mainAST]
  result <- pure False
-}
  hspec (unitTests unitTest2 unitTestType)