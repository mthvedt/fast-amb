{-# LANGUAGE
  GeneralizedNewtypeDeriving,
  Rank2Types,
  ScopedTypeVariables,
  ViewPatterns
#-}
-- To prevent the rewriting of properties we wanted to test, we have:
{-# OPTIONS_GHC
  -fno-enable-rewrite-rules
#-}

module Test.QuickCheck.Law where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans

import Test.QuickCheck
import Test.QuickCheck.Function

-- TODO: what test suites should we use if this lib is to be generic?
import Distribution.TestSuite.QuickCheck

type Harness c t = (Arbitrary c, Show c) => c -> t

class TestEq t where
  runEq :: t -> t -> Bool

-- A small list, of maximium size 4.
-- Needed because some of these tests get exponentially large.
-- Note that "ListT is not a monad transformer" -> we can't just pass in large lists and take 4,
-- because QuickCheck will always generate much larger lists.
newtype SmallList t = SmallList { unsmall :: [t] }
  deriving (Functor, Show)

instance Arbitrary t => Arbitrary (SmallList t) where
  arbitrary = SmallList <$> scale (min 4) arbitrary
  shrink (SmallList xss) = SmallList <$> shrink xss

-- Per Haskell's free theorems, any parameterized type which works on any given type parameter
-- works on all type parameters (if that parameter is unconstrained).
{-# ANN axiomFunctorId "HLint: ignore Functor law" #-}
axiomFunctorId :: (Functor f, TestEq (f Int)) => (c -> f Int) -> c -> Bool
axiomFunctorId h c = (id <$> fx) `runEq` fx where
  fx = h c

{-# ANN axiomFunctorComp "HLint: ignore Functor law" #-}
axiomFunctorComp :: (Functor f, TestEq (f Int)) =>
  (c -> f Int) -> c -> Fun Int Int -> Fun Int Int -> Bool
axiomFunctorComp h c (apply -> fn1) (apply -> fn2) = (fn2 . fn1 <$> fx) `runEq` (fmap fn2 . fmap fn1 $ fx) where
  fx = h c

-- TODO: applicative axioms
testFunctor :: (Functor f, TestEq (f Int), Arbitrary c, Show c) => String -> Harness c (f Int) -> Test
testFunctor typeclass_desc h = testGroup ("Functor axioms for " ++ typeclass_desc)
  [ testProperty "Functor identity law" $ axiomFunctorId h
  , testProperty "Functor composition law" $ axiomFunctorComp h
  ]

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, TestEq (m Int), Arbitrary c, Show c) => Harness c (m Int) -> Int -> Fun Int c -> Bool
axiomMonadLeftId h i (apply -> fcase) = (return i >>= f) `runEq` f i where
  f = h . fcase

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, TestEq (m Int), Arbitrary c, Show c) => Harness c (m Int) -> c -> Bool
axiomMonadRightId h c = (mx >>= return) `runEq` mx where
  mx = h c

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, TestEq (m Int), Arbitrary c, Show c) =>
  Harness c (m Int) -> c -> Fun Int c -> Fun Int c -> Bool
axiomMonadAssoc h c (apply -> fcase) (apply -> gcase) = ((mx >>= mf) >>= mg) `runEq` (mx >>= (mf >=> mg)) where
  mx = h c
  mf = h . fcase
  mg = h . gcase

testMonad :: (Monad m, TestEq (m Int), Arbitrary c, Show c) => String -> Harness c (m Int) -> Test
testMonad typeclass_desc h = testGroup ("Monad axioms for " ++ typeclass_desc)
  [ testFunctor typeclass_desc h
  , testProperty "Monad left identity law" $ axiomMonadLeftId h
  , testProperty "Monad right identity law" $ axiomMonadRightId h
  , testProperty "Monad associativity law" $ axiomMonadAssoc h
  ]

axiomMTId :: (MonadTrans t, Monad m, Monad (t m), TestEq (t m Int), Arbitrary c, Show c) =>
  Harness c (t m Int) -> Int -> Bool
axiomMTId (_w :: Harness c (t m Int)) i = (return i :: t m Int) `runEq` lift (return i)

-- TODO is this wrong?
axiomMTDistributive :: (MonadTrans t, Monad m, Monad (t m), TestEq (t m Int), Arbitrary c1, Show c1) =>
  Harness c0 (t m Int) -> Harness c1 (m Int) -> c1 -> Fun Int c1 -> Bool
axiomMTDistributive (h0 :: Harness c0 (t m Int)) h1 g (apply -> fcase) =
  lift (ma >>= mf) `runEq` ((lift ma :: t m Int) >>= (lift . mf)) where
    ma = h1 g
    mf = h1 . fcase

testMonadTrans :: (MonadTrans t, Monad m, Monad (t m), TestEq (t m Int),
    Arbitrary c0, Show c0, Arbitrary c1, Show c1) =>
  String -> Harness c0 (t m Int) -> Harness c1 (m Int) -> Test
testMonadTrans typeclass_desc h0 h1 =  testGroup ("MonadTrans axioms for " ++ typeclass_desc)
  [ testProperty "MonadTrans identity law" $ axiomMTId h0
  , testProperty "MonadTrans distributive law" $ axiomMTDistributive h0 h1
  ]
