{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  GeneralizedNewtypeDeriving,
  RankNTypes,
  TypeFamilies
#-}

module Amb where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State

import Data.Hashable
import qualified Data.HashMap.Lazy as Maps
import Data.Int
import qualified Data.Vector.Unboxed as Vectors

type Map = Maps.HashMap
type Vector = Vectors.Vector

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

-- This is the Scott encoding: a List represented as a manipulator of continuations.
-- For a nonempty list, we are provided a continuation that takes a head element and the rest of the list.
-- For the empty list, we are provided a 'failure continuation'; the second argument r.
-- The manipulator function is called the 'constructor'.
--
-- We don't bother making this a class since we will always use the Scott encoding,
-- which is the most general encoding we can use.
newtype AmbT m a = AmbT (forall r. (a -> AmbT m a -> m r) -> m r -> m r)

type Amb a = AmbT Identity a

listToAmb :: [a] -> AmbT m a
listToAmb = foldr ambcons ambnil

runAmb :: AmbT m a -> (a -> AmbT m a -> m r) -> m r -> m r
runAmb (AmbT cxr) = cxr

ambToList :: (Applicative m) => AmbT m a -> m [a]
ambToList mas = runAmb mas (\a mas1 -> (\as -> a:as) <$> ambToList mas1) (pure [])

instance Functor (AmbT f) where
  fmap fab (AmbT cxra) = AmbT $ \cb mb -> cxra (\a as -> cb (fab a) (fab <$> as)) mb

instance Applicative (AmbT a) where
  pure = return
  (<*>) = ap

instance Monad (AmbT m) where
  return x = listToAmb [x]
  as >>= famb = ambcat $ fmap famb as

instance MonadTrans AmbT where
  -- Interestingly, this is the only time we use m as a monad.
  lift m = AmbT $ \c i -> m >>= \x -> c x ambnil

ambnil :: AmbT m a
ambnil = AmbT $ \_ i -> i

ambcons :: a -> AmbT m a -> AmbT m a
ambcons x axs = AmbT $ \c _ -> c x axs
-- Given an amb-continuation c and an amb-of-amb axss,
-- creates a continuation that accepts a value a and concatenates the input amb to axss.
ambcatHelperInner :: (a -> AmbT m a -> m r) -> AmbT m (AmbT m a) -> a -> AmbT m a -> m r
ambcatHelperInner c axss x xs0 = c x $ ambcat $ ambcons xs0 axss
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> runAmb (ambcons xs0 axss) (ambcatHelper c i) i
-- ambcatHelperInner c axss x xs0 = c x $ Amb $ \c i -> ambcatHelper c i xs0 axss

-- We want to create a continuation Amb m a -> Amb m (Amb m a) -> m r
-- that uses the continuation c :: a -> Amb m a -> m r and the failure value m r.
ambcatHelper :: (a -> AmbT m a -> m r) -> m r -> AmbT m a -> AmbT m (AmbT m a) -> m r
ambcatHelper c i asx0 axss = runAmb asx0 (ambcatHelperInner c axss) (runAmb (ambcat axss) c i)

ambcat :: AmbT m (AmbT m a) -> AmbT m a
ambcat axaxs = AmbT $ \c i -> runAmb axaxs (ambcatHelper c i) i

instance Eq a => Eq (AmbT Identity a) where
  as == bs = runIdentity (ambToList as) == runIdentity (ambToList bs)

instance Show a => Show (AmbT Identity a) where
  show a = "Amb [" ++ show (ambToList a) ++ "]"

-- A query is a function that returns a FactReader, Amb monad.

newtype Entity = Entity Int32 deriving (Eq, Hashable, Ord)

newtype Tuple = Tuple (Vector Int32)

tupleToList :: Tuple -> [Entity]
tupleToList (Tuple t) = Entity <$> Vectors.toList t

newtype FactKey = TupleKey String

class BaseFact t where
  basekey :: t -> FactKey

data TupleFact = Fact {
  factkey :: FactKey,
  tuple :: Tuple
}

data FactEntry = NoEntry | Entry Tuple | SubIndex FactIndex

newtype FactIndex = FactIndex {
  subindices :: Map Entity (Either Tuple FactIndex)
}

newFactIndex :: FactIndex
newFactIndex = FactIndex Maps.empty

doLookup :: Entity -> FactIndex -> FactEntry
doLookup e idx = case Maps.lookup e $ subindices idx of
  Nothing -> NoEntry
  Just (Left t) -> Entry t
  Just (Right i) -> SubIndex i

newtype RuntimeError = RuntimeError String

-- TODO: this might be improved by making it a ScottList.
doPutFact :: (FactLogger m) => Tuple -> [Entity] -> FactIndex -> m FactIndex
doPutFact _ [] _ = throwRuntimeError "exhausted index"
doPutFact t (e:es) idx = do
  let idx0 = subindices idx
  subidx <- case Maps.lookup e idx0 of
    Just (Left t) -> throwRuntimeError "entity exists"
    Just (Right idx0) -> return idx0
    Nothing -> return newFactIndex
  entry <- case es of
    [] -> return $ Left t
    es -> Right <$> doPutFact t es subidx
  return . FactIndex $ Maps.insert e entry idx0

class Monad m => FactLogger m where
  throwRuntimeError :: String -> m t

class FactLogger m => FactReader m where
  type PartialResult m
  beginQuery :: Entity -> m (PartialResult m)
  refineQuery :: PartialResult m -> Entity -> m (PartialResult m)
  endQuery :: PartialResult m -> AmbT m Tuple

class FactLogger m => FactWriter m where
  putFact :: Tuple -> m ()

newtype FactBase = FactBase {
  baseIndex :: FactIndex
}

newtype FactState a = FactState (ExceptT RuntimeError (State FactBase) a) deriving (Functor, Applicative, Monad)

instance FactLogger FactState where
  throwRuntimeError s = FactState . throwError $ RuntimeError s

instance FactReader FactState where
  type PartialResult FactState = FactEntry
  beginQuery e = FactState $ do
    base <- lift get
    return . doLookup e $ baseIndex base
  refineQuery fe e = case fe of
    NoEntry -> throwRuntimeError "exhausted index"
    Entry t -> throwRuntimeError "exhausted entity"
    SubIndex i -> return $ doLookup e i
  endQuery fe = case fe of
    NoEntry -> lift $ throwRuntimeError "exhausted index" -- Shouldn't really happen
    Entry t -> lift $ return t
    SubIndex i -> lift $ throwRuntimeError "not yet implemented"

instance FactWriter FactState where
  putFact t = do
    base <- FactState $ lift get
    newbase <- doPutFact t (tupleToList t) $ baseIndex base
    FactState . lift . put $ FactBase newbase
