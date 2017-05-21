{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  Rank2Types,
  ScopedTypeVariables
#-}

module Control.Logic.Amb.Test (ambTests) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Foldable (toList)

import Control.Logic.Amb

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.QuickCheck.Law

import Distribution.TestSuite.QuickCheck

-- Tests that ambs are depth-first.
axiomDepthFirst :: (Amb a, TestEq (a Int), Arbitrary c, Show c) =>
  Harness c (a Int) -> SmallList (SmallList c) -> Bool
axiomDepthFirst h cases = ambcat (ambcat <$> xs) `runEq` join (ambcat <$> amb xs) where
  xs = unsmall $ unsmall . fmap h <$> cases

-- Tests the laws for ambuncons.
-- TODO this law doesn't tell us anything interesting about states.
-- * ambuncons $ amb as === return (first as, amb $ rest as) when as is non-empty
-- * ambuncons ambzero === ambzero
-- TODO remove constraints from Harness
unconsEqHelper :: (AmbLogic a, TestEq (a Int), Arbitrary c, Show c) =>
  Harness c (a Int) -> a (c, a c) -> a (c, a c) -> Bool
unconsEqHelper h x y = fstEq x y && sndEq x y where
 fstEq x y = join (h . fst <$> x) `runEq` join (h . fst <$> y)
 sndEq x y = join (join . fmap h . snd <$> x) `runEq` join (join . fmap h . snd <$> y)

axiomUncons :: (AmbLogic a, TestEq (a Int), Arbitrary c, Show c) =>
  Harness c (a Int) -> [c] -> Bool
axiomUncons (h :: Harness c (a Int)) [] = unconsEqHelper h (ambuncons ambzero :: a (c, a c)) ambzero
axiomUncons h (c:cs) = unconsEqHelper h (ambuncons $ amb (c:cs)) $ return (c, amb cs)

-- -- Test that taking the first N from an amb is equivalent to taking n, then amb.
-- -- Especially important when a is a monad transformer.
-- axiomLazyTake :: (AmbLogic a, TestEq (a Int), Arbitrary c, Show c) =>
--   Harness c (a Int) -> Int -> [c] -> Bool
-- axiomLazyTake h i0 cs = flatten (amb cases1) `runEq` flatten cases2 where
--   i = i0 `mod` max 1 (length cs)
--   -- cases1 :: [c]
--   cases1 = take i cs
--   -- cases2 :: a c
--   -- TODO: observeMany should return a c
--   cases2 = join $ amb . fst <$> observeMany i (amb cs)
--   -- flatten :: a c -> a Int
--   flatten cases = join $ h <$> cases

testAmb :: (AmbLogic a, TestEq (a Int), Arbitrary c, Show c) => String -> Harness c (a Int) -> Test
testAmb typeclass_desc h = testGroup ("Amb tests for " ++ typeclass_desc)
  [ testMonad typeclass_desc h
  , testProperty "Ambs are depth-first" $ axiomDepthFirst h
  , testProperty "Uncons works" $ axiomUncons h
  -- , testProperty "Observe works and is fully lazy" $ axiomLazyTake h
  ]

type AmbTHarness c a m = AmbTrans a m => Harness (SmallList (Maybe c)) (a m Int)

ambTHarness :: (AmbTrans a m, Arbitrary c, Show c) => Harness c (m Int) -> AmbTHarness c a m
ambTHarness g0 gs = let toAmb (Just v) = lift v
                        toAmb Nothing = afail
                        gs' = fmap g0 <$> gs
                        amblist = toAmb <$> unsmall gs'
                    in ambcat amblist

instance (AmbTrans a Identity, Eq t) => TestEq (a Identity t) where
  runEq = ambEq

instance (AmbTrans a (State Int), Eq t) => TestEq (a (State Int) t) where
  a `runEq` b = runState (toMaybeListM a) 1 == runState (toMaybeListM b) 1

testAmbT :: (AmbTrans a Identity, AmbTrans a (State Int), AmbLogic (a Identity), AmbLogic (a (State Int)),
  TestEq (a Identity Int), TestEq (a (State Int) Int)) =>
  String -> a Identity Int -> Test
testAmbT typeclass_desc (_witness :: a Identity Int) = testGroup ("AmbT suite tests for " ++ typeclass_desc)
  [ testAmb typeclass_desc hId
  , testMonadTrans typeclass_desc (return 1 :: a (State Int) Int)
  , testAmb (typeclass_desc ++ " (as State transformer)") hAmbT
  ] where
    hId :: AmbTHarness Int a Identity
    hId = ambTHarness return
    hAmbT :: AmbTHarness (Int, Fun Int Int) a (State Int)
    hAmbT = ambTHarness stateHarness

ambTests :: Test
ambTests = testGroup "Control.Logic.Amb"
  [ testAmbT "ChurchAmb" (return 1 :: ChurchAmb Int)
  -- , testCase "ScottAmb" (return 1 :: ScottAmb Int)
  -- , testCase "ParigotAmb" (return 1 :: ParigotAmb Int)
  -- , testCase "FastAmb" (return 1 :: FastAmb Int)
  ]
