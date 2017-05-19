{-# LANGUAGE
  GeneralizedNewtypeDeriving,
  Rank2Types,
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

stateHarness :: (Int, Fun Int Int) -> State Int Int
stateHarness (x, apply -> f) = state $ \s -> (x, f s)

class TestEq t where
  runEq :: t -> t -> Bool

-- A small list, of maximium size 4.
-- Needed because some of these tests get exponentially large.
-- Note that we can't write tests with larger lists then take 4,
-- because QuickCheck will always generate the full list.
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

axiomMonadMorphId :: (Monad a, Monad b, TestEq (b Int)) => (forall x. a x -> b x) -> Int -> Bool
-- axiomMTId (_w :: Harness c (t m Int)) morph i = (return i :: t m Int) `runEq` lift (return i)
axiomMonadMorphId morph i = morph (return i) `runEq` return i

-- TODO is this wrong?
axiomMTDistributive :: (Monad a, Monad b, TestEq (b Int), Arbitrary c, Show c) =>
  Harness c (a Int) -> (forall x. a x -> b x) -> c -> Fun Int c -> Bool
axiomMTDistributive h morph g (apply -> fcase) =
  morph (ma >>= mf) `runEq` (morph ma >>= (morph . mf)) where
    ma = h g
    mf = h . fcase

testMonadMorph :: (Monad a, Monad b, TestEq (b Int), Arbitrary c, Show c) =>
  String -> Harness c (a Int) -> (forall x. a x -> b x) -> Test
testMonadMorph morph_desc h morph = testGroup ("MonadMorph axioms for " ++ morph_desc)
  [ testProperty "MonadMorph identity law" $ axiomMonadMorphId morph
  , testProperty "MonadMorph distributive law" $ axiomMTDistributive h morph
  ]

-- Using this newtype and a type witness is the only way I could get lift to have the proper kindedness,
-- forall x. m x -> (t m) x. GHC's kind inference behaves oddly sometimes.
newtype LowerKind m x = LowerKind (m x)
  deriving (Functor, Applicative, Monad, TestEq)

typedLift :: (Monad m, MonadTrans t) => t m Int -> m x -> LowerKind (t m) x
typedLift _w mx = LowerKind $ lift mx

-- Like TestMonadMorph, but with MonadTrans-specific messages. Callers must provide a type witness
-- of the type t (State Int) Int.
testMonadTrans :: (MonadTrans t, Monad (t (State Int)), TestEq (t (State Int) Int)) =>
  String -> t (State Int) Int -> Test
testMonadTrans typeclass_desc _w = testGroup ("MonadTrans axioms for " ++ typeclass_desc)
  [ testProperty "MonadTrans identity law" $ axiomMonadMorphId $ typedLift _w
  , testProperty "MonadTrans distributive law" $ axiomMTDistributive stateHarness $ typedLift _w
  ]
