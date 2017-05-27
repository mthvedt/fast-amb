{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  Rank2Types,
  ScopedTypeVariables
#-}

module Control.Monad.Logic.Amb.Test (ambTests) where

import qualified Control.Arrow as Arrow
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Foldable (toList)

import Control.Monad.Logic

import Control.Monad.Logic.Amb
import Control.Monad.Logic.Run

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.QuickCheck.Law

import Distribution.TestSuite.QuickCheck

unconsEqHelper :: (MonadLogic l, TestEq (l Int)) => l (Maybe (Int, l Int)) -> l (Maybe (Int, l Int)) -> Bool
unconsEqHelper x y = fstEq x y && sndEq x y where
  fstEq x y = (maybe (-1) fst <$> x) `runEq` (maybe (-1) fst <$> y)
  sndEq x y = join (maybe mzero snd <$> x) `runEq` join (maybe mzero snd <$> y)

axiomSplit :: (MonadLogic l, TestEq (l Int)) => (c -> l Int) -> [c] -> Bool
axiomSplit h [] = unconsEqHelper (msplit (mzero `asTypeOf` h undefined)) $ return Nothing
axiomSplit h cs = msplit (ambcat (a:as)) `unconsEqHelper` join (injcat <$> msplit a) where
  injcat (Just (t, ts)) = return $ Just (t, ambcat (ts:as))
  injcat Nothing = msplit $ ambcat as
  (a:as) = h <$> cs

testLogic :: (MonadLogic l, TestEq (l Int), Arbitrary c, Show c) => String -> (c -> l Int) -> Test
testLogic typeclass_desc h = testGroup ("MonadLogic tests for " ++ typeclass_desc)
  [ testMonadPlus typeclass_desc h
  , testProperty "Split gets head and tail" $ axiomSplit h
  -- , testProperty "Observe works and is fully lazy" $ axiomLazyTake h
  ]

logicTHarness :: (MonadTrans l, Monad m, MonadLogic (l m)) => (c -> m Int) -> SmallList c -> l m Int
logicTHarness h0 cs = amblift $ h0 <$> cs

instance TestEq (AmbT Identity Int) where
  a `runEq` b = runIdentity (a `logicEq` b)

instance TestEq (AmbT (State Int) Int) where
  a `runEq` b = runState (logicToList a) 1 == runState (logicToList b) 1

testLogicT :: (MonadTrans l, MonadLogic (l Identity), MonadLogic (l (State Int)),
  TestEq (l Identity Int), TestEq (l (State Int) Int)) =>
  String -> l Identity Int -> Test
testLogicT typeclass_desc (_witness :: l Identity Int) = testGroup ("AmbT suite tests for " ++ typeclass_desc)
  [ testLogic typeclass_desc hId
  , testMonadTrans typeclass_desc (return 1 :: l (State Int) Int)
  , testLogic (typeclass_desc ++ " (as State transformer)") hT
  ] where
    hId :: SmallList Int -> l Identity Int
    hId = logicTHarness return
    hT :: SmallList (Int, Fun Int Int) -> l (State Int) Int
    hT = logicTHarness stateHarness

ambTests :: Test
ambTests = testGroup "Control.Logic.Amb"
  [ testLogicT "FastAmb" (return 1 :: Amb Int)
  -- , testCase "ScottAmb" (return 1 :: ScottAmb Int)
  -- , testCase "ParigotAmb" (return 1 :: ParigotAmb Int)
  -- , testCase "FastAmb" (return 1 :: FastAmb Int)
  ]
