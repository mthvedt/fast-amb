{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  MultiParamTypeClasses,
  RankNTypes
#-}

-- TODO: test infinite

module Control.Monad.Logic.Amb (Amb, AmbT, amb, ambcat, amblift) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans

import Control.Monad.Logic.Class

import Control.Monad.Logic.Run

-- | 'AmbT' is a 'MonadLogic' and transformer of monads.
-- | Amb provides both fair search and concatenation in constant time, making it a theoretically
-- | ideal choice for a variety of backtracking search strategies.
-- |
-- | Amb is isomorphic to the "ListT done right" monad or Oleg's
-- | LogicT monad. Unlike ListT and "ListT done right", Amb provides concatenation in
-- | constant time. Unlike LogicT, Amb also provides 'split' in constant (and fast) time, making
-- | deep fair searches possible. (TODO: example)
newtype AmbT m x = AmbT {
  runAmbT :: forall r. AmbT m x -> (x -> AmbT m x -> m r -> m r) -> m r -> m r
}

-- | The basic Amb monad. Isomorphic to List.
type Amb = AmbT Identity

instance Functor (AmbT f) where
  -- TODO how does this perform?
  {-# INLINE fmap #-}
  fmap = liftM
  -- fmap f xs = AmbT $ \rest cy z -> let
  --   cx x xrest = cy (f x) $ (f <$> xrest) `mplus` rest
  --   in runAmbT xs undefined cx z

instance Applicative (AmbT a) where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = ap
  -- fs <*> xs = AmbT $ \rest cy z -> let
  --   cf f frest = runAmbT xs undefined cx where
  --     cx x xrest = cy (f x) $ (frest <*> xs) `mplus` rest
  --   in runAmbT fs undefined cf z

instance Monad (AmbT m) where
  {-# INLINABLE return #-}
  return x = AmbT $ \rest c z -> c x rest z
  -- {-# INLINABLE >>= #-}
  -- Two important performance benefits follow from doing things this way.
  -- One, the user-supplied destructor, cy, is not altered. Two, the rest parameter is
  -- only modified once in a way that is left recursive. So each bind operation
  -- is only O(n) in the size of xs0, even if msplit is called often.
  {-# INLINABLE (>>=) #-}
  xs >>= f = AmbT $ \rest cy z -> let
    cx x xrest = runAmbT (f x) ((xrest >>= f) <|> rest) cy
    in runAmbT xs mzero cx z

-- instance Amb (AmbT m) where
--   amb [] = mzero
--   amb (x:xs) = AmbT $ \rest c z -> c x (axs `mplus` rest) $ runFastAmbT axs rest c z where
--     axs = amb xs

instance Alternative (AmbT m) where
  {-# INLINABLE empty #-}
  empty = AmbT $ \_ _ z -> z
  {-# INLINABLE (<|>) #-}
  a <|> b = AmbT $ \rest c z -> runAmbT a (b <|> rest) c $ runAmbT b rest c z

instance MonadPlus (AmbT m) where
  {-# INLINE mzero #-}
  mzero = empty
  {-# INLINE mplus #-}
  mplus = (<|>)

instance MonadTrans AmbT where
  -- Note that we use m as a monad only in MonadTrans and MonadLogic.
  -- This means that almost everyhing we know about m goes in the destructor,
  -- where it can more easily be inlined.
  {-# INLINABLE lift #-}
  lift mx = AmbT $ \rest c z -> mx >>= \x -> c x rest z

instance Monad m => MonadLogic (AmbT m) where
  {-# INLINABLE msplit #-}
  msplit a = lift . runAmbT a mzero c $ return Nothing where
    c t rest _ = return $ Just (t, rest)

instance Monad m => RunLogicT m (AmbT m) where
  -- Here we see the advantage of laziness: the _xs args are never used.
  {-# INLINABLE runLogicT #-}
  runLogicT cf = go where go z0 xs0 = runAmbT xs0 mzero (\x _xs z -> cf x z) z0

-- TODO: does show (m [a]) work?
instance Show a => Show (Amb a) where
  show as = "FastAmb" ++ runIdentity (logicShow as)

amb :: (Foldable f, MonadPlus m) => f x -> m x
{-# INLINE amb #-}
amb = foldr (mplus . return) mzero

ambcat :: (Foldable f, MonadPlus m) => f (m x) -> m x
{-# INLINE ambcat #-}
ambcat = join . amb

amblift :: (Foldable f, Monad m, MonadTrans t, MonadPlus (t m)) => f (m x) -> t m x
{-# INLINE amblift #-}
amblift = foldr (mplus . lift) mzero
