{-# LANGUAGE
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  RankNTypes,
  ScopedTypeVariables,
  TypeFamilies
#-}

module Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.HashMap.Lazy (HashMap)
import qualified Data.Vector as BoxedVectors
import qualified Data.Vector.Unboxed as UnboxedVectors

type BoxedVector = BoxedVectors.Vector
type UnboxedVectors = UnboxedVectors.Vector

-- begin free monad experiment

-- Church-encoded free monad, accepting two continuations.
-- The first continuation deals with a pure 'boxed' value.
-- The second collapses the boxed f's inside the free monad.
-- newtype Free r f a = Free ((a -> r) -> (f r -> r) -> r)
--
-- runFree :: Free r f a -> (a -> r) -> (f r -> r) -> r
-- runFree (Free cxr) = cxr
--
-- instance Functor (Free r f) where
--   fmap = liftM
--
-- instance Applicative (Free r f) where
--   pure = return
--   (<*>) = ap
--
-- instance Monad (Free r f) where
--   return x = Free $ \jc _ -> jc x
--   (Free cxr) >>= bindf = Free $ \jc fc -> cxr (\x -> runFree (bindf x) jc fc) fc
--
-- instance MonadTrans (Free r) where
--    lift m = Free (\jc fc -> fc (jc <$> m))

-- end free monad experiment

class (Monad m) => MonadAmb m where
  amb :: [t] -> m t
  ambcat :: m (m t) -> m t

-- We might extend this later
-- This is the Scott encoding: a List represented as a manipulator of continuations.
-- For a nonempty list, we are provided a continuation that takes a head element and the rest of the list.
-- For the empty list, we are provided a 'failure continuation'; the second argument r.
-- The manipulator function is called the 'constructor'.
newtype Amb m a = Amb (forall r. (a -> Amb m a -> m r) -> m r -> m r)

runAmb :: Amb m a -> (a -> Amb m a -> m r) -> m r -> m r
runAmb (Amb cxr) = cxr

instance Functor (Amb f) where
  fmap fab (Amb cxra) = Amb $ \cb mb -> cxra (\a as -> cb (fab a) (fab <$> as)) mb

instance Applicative (Amb a) where
  pure x = ambcons x ambnil
  afs <*> axs = ambcat $ fmap (`fmap` axs) afs

instance Monad (Amb m) where
  return = pure
  as >>= famb = ambcat $ fmap famb as

instance MonadTrans Amb where
  -- Interestingly, this is the only time we use m as a monad.
  lift m = Amb $ \c i -> m >>= \x -> c x ambnil

ambnil :: Amb m a
ambnil = Amb $ \_ i -> i

ambcons :: a -> Amb m a -> Amb m a
ambcons x axs = Amb $ \c _ -> c x axs

-- Given an amb-continuation c and an amb-of-amb axss,
-- creates a continuation that accepts a value a and concatenates the input amb to axss.
ambcatHelperInner :: (a -> Amb m a -> m r) -> Amb m (Amb m a) -> a -> Amb m a -> m r
ambcatHelperInner c axss x xs0 = c x $ ambcat $ ambcons xs0 axss
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> runAmb (ambcons xs0 axss) (ambcatHelper c i) i
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> ambcatHelper c i xs0 axss

-- We want to create a continuation Amb m a -> Amb m (Amb m a) -> m r
-- that uses the continuation c :: a -> Amb m a -> m r and the failure value m r.
ambcatHelper :: (a -> Amb m a -> m r) -> m r -> Amb m a -> Amb m (Amb m a) -> m r
ambcatHelper c i asx0 axss = runAmb asx0 (ambcatHelperInner c axss) (runAmb (ambcat axss) c i)

instance MonadAmb (Amb m) where
  amb = foldr ambcons (Amb (\ _ i -> i))
  ambcat axaxs = Amb $ \c i -> runAmb axaxs (ambcatHelper c i) i

-- class FactQuery q where
--   type Result q
--   query :: (FactSystem m) => q -> m () -> Amb m (Result q)

newtype Entity = Entity Int

newtype Tuple = UnboxedVector Int

newtype FactKey = TupleKey String

class BaseFact t where
  basekey :: t -> FactKey

data TupleFact = Fact {
  factkey :: FactKey,
  tuple :: Tuple
}

-- class FactTuple t where
--   tuplekey :: t -> TupleKey

data FactSubindexEntry = NoIndex | DirectIndex | SubIndex

data FactIndex = FactIndex {
  subindices :: BoxedVector FactSubindexEntry
}

{-
What characterizes a fact?
Queries and facts should be their own class, representable in a FactSystem.
-}
class FactQuery f where
  type FactType f
  type QueryInfo f
  queryFact :: f -> QueryInfo f -> FactType f

class Monad m => FactReader m where
  -- queryFact :: (FactQuery f) => f -> m r

class FactReader m => FactWriter m where
  putFact :: (BaseFact t) => t -> m ()

data FactBase = FactBase {
  -- bases :: HashMap BaseFact FactIndex
}

-- doQueryFact :: FactBase -> (r, FactBase)
--
-- doPutFact :: (BaseFact t) => FactBase -> t -> FactBase

-- impl

data FactSystemImpl = FactSystemImpl {
  persistentsystem :: FactBase,
  tempsystem :: ()
}

newtype FactSystem m a = FactSystem (StateT FactSystemImpl m a) deriving (Functor, Applicative, Monad)

-- newtype Fact f = Fact f

-- class FactCont m f where
  -- runFact :: m a -> Fact f -> a
