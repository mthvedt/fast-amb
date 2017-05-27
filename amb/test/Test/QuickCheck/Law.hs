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

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Data.Monoid

import Test.QuickCheck
import Test.QuickCheck.Function

-- TODO: what test suites should we use if this lib is to be generic?
import Distribution.TestSuite.QuickCheck

stateHarness :: (Int, Fun Int Int) -> State Int Int
stateHarness (x, apply -> f) = state $ \s -> (x, f s)

class TestEq t where
  runEq :: t -> t -> Bool

-- A small list, of maximium size 4.
-- Needed because some of these tests get exponentially large.
-- Note that we can't write tests with larger lists then take 4,
-- because QuickCheck will always generate the full list.
newtype SmallList t = SmallList { unsmall :: [t] }
  deriving (Foldable, Functor, Show)

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

testFunctor :: (Functor f, TestEq (f Int), Arbitrary c, Show c) => String -> (c -> f Int) -> Test
testFunctor typeclass_desc h = testGroup ("Functor axioms for " ++ typeclass_desc)
  [ testProperty "Functor identity law" $ axiomFunctorId h
  , testProperty "Functor composition law" $ axiomFunctorComp h
  ]

axiomApplicativeId :: (Applicative a, TestEq (a Int)) => (c -> a Int) -> c -> Bool
axiomApplicativeId h c = (pure id <*> ax) `runEq` ax where
  ax = h c

axiomApplicativeComp :: (Applicative a, TestEq (a Int)) =>
  (c -> a Int) -> c -> c -> c -> Fun (Int, Int) Int -> Fun (Int, Int) Int -> Bool
axiomApplicativeComp h c1 c2 c3 (apply -> f) (apply -> g) =
  (pure (.) <*> af <*> ag <*> ax) `runEq` (af <*> (ag <*> ax)) where
    af = curry f <$> h c1
    ag = curry g <$> h c2
    ax = h c3

axiomApplicativeHomomoprhism :: (Applicative a, TestEq (a Int)) =>
  (c -> a Int) -> Int -> Fun Int Int -> Bool
axiomApplicativeHomomoprhism _w i (apply -> f) = (pure f <*> pure i) `runEq` (pure (f i) `asTypeOf` _w undefined)

axiomApplicativeInterchange :: (Applicative a, TestEq (a Int)) =>
  (c -> a Int) -> c -> Int -> Fun (Int, Int) Int -> Bool
axiomApplicativeInterchange h c i (apply -> f) = (af <*> pure i) `runEq` (pure ($ i) <*> af) where
  af = curry f <$> h c

-- TODO: test fmap behavior is consistent with pure/<*> instead of testFunctor
testApplicative :: (Applicative a, TestEq (a Int), Arbitrary c, Show c) => String -> (c -> a Int) -> Test
testApplicative typeclass_desc h = testGroup ("Applicative axioms for " ++ typeclass_desc)
  [ testFunctor typeclass_desc h
  , testProperty "Applicative identity law" $ axiomApplicativeId h
  , testProperty "Applicative composition law" $ axiomApplicativeComp h
  , testProperty "Applicative homomorphism law" $ axiomApplicativeHomomoprhism h
  , testProperty "Applicative interchange law" $ axiomApplicativeInterchange h
  ]

{-# ANN axiomMonadLeftId "HLint: ignore Monad law, left identity" #-}
axiomMonadLeftId :: (Monad m, TestEq (m Int)) => (c -> m Int) -> Int -> Fun Int c -> Bool
axiomMonadLeftId h i (apply -> fcase) = (return i >>= f) `runEq` f i where
  f = h . fcase

{-# ANN axiomMonadRightId "HLint: ignore Monad law, right identity" #-}
axiomMonadRightId :: (Monad m, TestEq (m Int)) => (c -> m Int) -> c -> Bool
axiomMonadRightId h c = (mx >>= return) `runEq` mx where
  mx = h c

{-# ANN axiomMonadAssoc "HLint: ignore Functor law" #-}
axiomMonadAssoc :: (Monad m, TestEq (m Int)) =>
  (c -> m Int) -> c -> Fun Int c -> Fun Int c -> Bool
axiomMonadAssoc h c (apply -> fcase) (apply -> gcase) = ((mx >>= mf) >>= mg) `runEq` (mx >>= (mf >=> mg)) where
  mx = h c
  mf = h . fcase
  mg = h . gcase

  -- TODO: test applicative behavior is consistent with bind/return instead of testApplicative
testMonad :: (Monad m, TestEq (m Int), Arbitrary c, Show c) => String -> (c -> m Int) -> Test
testMonad typeclass_desc h = testGroup ("Monad axioms for " ++ typeclass_desc)
  [ testApplicative typeclass_desc h
  , testProperty "Monad left identity law" $ axiomMonadLeftId h
  , testProperty "Monad right identity law" $ axiomMonadRightId h
  , testProperty "Monad associativity law" $ axiomMonadAssoc h
  ]

axiomMonoidLeftId :: (Monoid m, TestEq m) => (c -> m) -> c -> Bool
axiomMonoidLeftId h c = (mempty <> m) `runEq` m where m = h c

axiomMonoidRightId :: (Monoid m, TestEq m) => (c -> m) -> c -> Bool
axiomMonoidRightId h c = (m <> mempty) `runEq` m where m = h c

axiomMonoidAssoc :: (Monoid m, TestEq m) => (c -> m) -> c -> c -> c -> Bool
axiomMonoidAssoc h c1 c2 c3 = ((m1 <> m2) <> m3) `runEq` (m1 <> (m2 <> m3)) where
  [m1, m2, m3] = h <$> [c1, c2, c3]

testMonoid :: (Monoid m, TestEq m, Arbitrary c, Show c) => String -> (c -> m) -> Test
testMonoid typeclass_desc h = testGroup ("Monoid axioms for " ++ typeclass_desc)
  [ testProperty "Monoid left identity law" $ axiomMonoidLeftId h
  , testProperty "Monoid right identity law" $ axiomMonoidRightId h
  , testProperty "Monoid associativity law" $ axiomMonoidAssoc h
  ]

newtype AlternativeMonoid a x = AlternativeMonoid (a x)

instance Alternative a => Monoid (AlternativeMonoid a x) where
  mempty = AlternativeMonoid empty
  mappend (AlternativeMonoid a) (AlternativeMonoid b) = AlternativeMonoid (a <|> b)

instance TestEq (a x) => TestEq (AlternativeMonoid a x) where
  runEq (AlternativeMonoid a) (AlternativeMonoid b) = runEq a b

testAlternative :: (Alternative a, TestEq (a Int), Arbitrary c, Show c) => String -> (c -> a Int) -> Test
testAlternative typeclass_desc h = testGroup ("MonadPlus axioms for " ++ typeclass_desc)
  [ testMonoid (typeclass_desc ++ " (as Alternative monoid)") h2
  , testApplicative typeclass_desc h
  ] where
  h2 = AlternativeMonoid . h

newtype MonadPlusMonoid m x = MonadPlusMonoid (m x)

instance MonadPlus m => Monoid (MonadPlusMonoid m x) where
  mempty = MonadPlusMonoid mzero
  mappend (MonadPlusMonoid a) (MonadPlusMonoid b) = MonadPlusMonoid (a `mplus` b)

instance TestEq (m x) => TestEq (MonadPlusMonoid m x) where
  runEq (MonadPlusMonoid a) (MonadPlusMonoid b) = runEq a b

-- TODO: test mplus === Alternative isomorphism instead of testAlternative
testMonadPlus :: (MonadPlus a, TestEq (a Int), Arbitrary c, Show c) => String -> (c -> a Int) -> Test
testMonadPlus typeclass_desc h = testGroup ("MonadPlus axioms for " ++ typeclass_desc)
  [ testMonad typeclass_desc h
  , testMonoid (typeclass_desc ++ " (as Alternative monoid)") h2
  , testMonoid (typeclass_desc ++ " (as MonadPlus monoid)") h2
  ] where
  h2 = MonadPlusMonoid . h

-- TODO: monoid morphs
axiomMonadMorphId :: (Monad a, Monad b, TestEq (b Int)) => (forall x. a x -> b x) -> Int -> Bool
axiomMonadMorphId morph i = morph (return i) `runEq` return i

-- TODO is this wrong?
axiomMTDistributive :: (Monad a, Monad b, TestEq (b Int), Arbitrary c, Show c) =>
  (c -> a Int) -> (forall x. a x -> b x) -> c -> Fun Int c -> Bool
axiomMTDistributive h morph g (apply -> fcase) =
  morph (ma >>= mf) `runEq` (morph ma >>= (morph . mf)) where
    ma = h g
    mf = h . fcase

testMonadMorph :: (Monad a, Monad b, TestEq (b Int), Arbitrary c, Show c) =>
  String -> (c -> a Int) -> (forall x. a x -> b x) -> Test
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
-- TODO: how can we test arbitrary transformers?
testMonadTrans :: (MonadTrans t, Monad (t (State Int)), TestEq (t (State Int) Int)) =>
  String -> t (State Int) Int -> Test
testMonadTrans typeclass_desc _w = testGroup ("MonadTrans axioms for " ++ typeclass_desc)
  -- [ testMonad (typeclass_desc ++ " (as Identity transformer)")
  -- , testMonad (typeclass_desc ++ " (as State transformer)")
  -- , testProperty "MonadTrans identity law" $ axiomMonadMorphId $ typedLift _w
  [ testProperty "MonadTrans identity law" $ axiomMonadMorphId $ typedLift _w
  , testProperty "MonadTrans distributive law" $ axiomMTDistributive stateHarness $ typedLift _w
  ]
