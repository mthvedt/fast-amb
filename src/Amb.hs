{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  MultiParamTypeClasses,
  RankNTypes
#-}

module Amb where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import qualified Control.Monad.State as HState

import Data.Hashable
import qualified Data.HashMap.Lazy as Maps
import Data.Int
import qualified Data.Vector.Unboxed as Vectors

type Map = Maps.HashMap
type Vector = Vectors.Vector

-- class Suspension s where
--   type Input s
--
-- data Suspended e m t = Suspended {
--   suspension :: e,
--   resume :: Input e -> m t
-- }

class Monad m => AmbInterpreter m where
  interpret :: t -> t -> m t
  interpretFail :: t -> m t

-- TODO: foldable
class Monad a => Amb a where
  -- The reason we use [], instead of the more general Foldable, is because amb must be strict in the LHS but not
  -- the RHS of the fold. The [] functor encapsulates this naturally.
  -- TODO: that's not really what we want. We want a more general "ChurchScott" amb, which can be folded either way.
  -- It can opt to use the Church fold or a destructive Scott encoding. In particular, we need destructo-Scott
  -- for continuations to work.
  amb :: [t] -> a t
  fail :: a ()

class Amb a => Logic a where
  first :: a t -> (t, a t)

-- TODO: newtype ChurchList

-- class Amb m => AmbState m where
--   type State m
--   get :: m (State m)
--   put :: State m -> m ()
-- TODO: do we need the m?
-- TODO: is it faster if we don't use forall?

-- TODO: do we need the m?
-- TODO: is it faster if we don't use forall?
-- This is a slightly more complicated continuation-passing encoding of a Scott list with failure.
-- It's designed to combine the strictness and efficiency of foldl with the tail-recursion and laziness of foldr.
-- Alternately, combining the simplicity of a Foldable/Church list with the efficiency of a Scott list.
-- TODO: test the above assertions.
-- TODO: this doesn't work great. Does it make sense to use a State monad? How do we do state here?
-- newtype AmbT m t = AmbT { runAmbT :: forall r. (m r -> t -> AmbT m t -> m r) -> (m r -> AmbT m t -> m r) -> m r -> m r }

-- TODO: This is the Church amb, which should be the fastest Amb. Test it.
-- We put m r everywhere so ChurchAmbT never has to use the underlying bind.
-- Since m is usually a monad, this is strictly more powerful anyway.
-- We need m in the ChurchAmb type so we can make it a monad transformer later.
newtype ChurchAmbT m t = ChurchAmbT { runChurchAmbT :: forall r. (t -> m r -> m r) -> (m r -> m r) -> m r -> m r }

-- TODO: how about Maybe a?
-- ambToList :: (Applicative m) => AmbT m a -> m [a]
-- ambToList mas = runAmb mas (\a mas1 -> (\as -> a:as) <$> ambToList mas1) (\mas1 -> ambToList mas1) (pure [])

type ChurchAmb = ChurchAmbT Identity

instance Functor (ChurchAmbT f) where
  fmap = liftM

instance Applicative (ChurchAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ChurchAmbT m) where
  return x = amb [x]
  -- note that f is called for failures in both the lhs and the rhs.
  -- Also, because both the outer and inner runAmbs are right-associative, we have proper right-associativity
  -- which yields the laziness and O(n) asymptotics we need.
  -- TODO: test both above assertions.
  -- TODO: test the underlying binding is correct. It should be. See 'ListT done right' for test ideas.
  xs >>= fxys = ChurchAmbT $ \c f z0 -> runChurchAmbT xs (\x z1 -> runChurchAmbT (fxys x) c f z1) f z0

instance Amb (ChurchAmbT m) where
  amb xs = ChurchAmbT $ \c _ z -> foldr c z xs
  fail = ChurchAmbT $ \_ f z -> f z

instance MonadTrans ChurchAmbT where
  -- The only time we use m as a monad.
  lift mx = ChurchAmbT $ \c _ z -> mx >>= \x -> c x z

churchAmbToList :: Monad m => ChurchAmbT m t -> m [t]
churchAmbToList a = runChurchAmbT a (fmap . (:)) id (return [])

instance Eq a => Eq (ChurchAmbT Identity a) where
  as == bs = runIdentity (churchAmbToList as) == runIdentity (churchAmbToList bs)

instance Show a => Show (ChurchAmbT Identity a) where
  show a = "ChurchAmb [" ++ show (churchAmbToList a) ++ "]"

newtype ScottAmbT m t = ScottAmbT {
  runScottAmbT :: forall r. (t -> ScottAmbT m t -> m r) -> (ScottAmbT m t -> m r) -> m r -> m r
}

type ScottAmb = ScottAmbT Identity

instance Functor (ScottAmbT f) where
  -- Need to define fmap because we use it in >>=
  fmap f xs0 = ScottAmbT $ \cy fy z -> let
    cx x xs = cy (f x) $ f <$> xs
    fx xs = fy $ f <$> xs
    in runScottAmbT xs0 cx fx z

instance Applicative (ScottAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ScottAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  xs0 >>= fxys = scottJoin $ fxys <$> xs0 where
    scottJoin xss0 = ScottAmbT $ \c0 f0 z0 -> let
      cxs xs0 xss = let cx x xs = c0 x $ combine xs xss
                        fx xs = f0 $ combine xs xss
                        zx = runScottAmbT xss cxs fxs z0
                        combine a as = scottJoin $ ScottAmbT $ \ca _ _ -> ca a as
                    in runScottAmbT xs0 cx fx zx
      fxs xss = f0 $ scottJoin xss
      in runScottAmbT xss0 cxs fxs z0

instance Amb (ScottAmbT m) where
  amb [] = ScottAmbT $ \_ _ z -> z
  amb (x:xs) = ScottAmbT $ \c _ _ -> c x $ amb xs
  fail = ScottAmbT $ \_ f _ -> f $ amb []

instance MonadTrans ScottAmbT where
  -- The only time we use m as a monad.
  lift mx = ScottAmbT $ \c _ _ -> mx >>= \x -> c x $ amb []

scottAmbToList :: Monad m => ScottAmbT m t -> m [t]
scottAmbToList a = runScottAmbT a (\x xs -> (x:) <$> scottAmbToList xs) scottAmbToList (return [])

instance Eq a => Eq (ScottAmbT Identity a) where
  as == bs = runIdentity (scottAmbToList as) == runIdentity (scottAmbToList bs)

instance Show a => Show (ScottAmbT Identity a) where
  show a = "ScottAmb [" ++ show (scottAmbToList a) ++ "]"
