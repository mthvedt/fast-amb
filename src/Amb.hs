{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  MultiParamTypeClasses,
  RankNTypes,
  TypeFamilies
#-}

-- Continuation-passing implementation of Amb.
-- Inspired by https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf.

module Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Foldable (toList)

class (Monad m, m ~ Target f) => AmbResult f m where
  type Target f :: * -> *
  -- Note that although laziness is not guaranteed, this is at least strict in the wrapping monad.
  -- So it does not support, for example, partial evaluation of monads with side effects.
  -- If you want to only partially evaluate the underlying monad, use ambHead.
  ambFoldRT :: (t -> r -> r) -> (r -> r) -> r -> f t -> m r
  -- ambHead :: Int -> f t -> f t

-- TODO test all of these
ambFoldLT' :: (AmbResult f m) => (r -> t -> r) -> (r -> r) -> r -> f t -> m r
ambFoldLT' cf ff z f = ambFoldRT cfl ffl id f <*> return z where
  -- This transforms a list into a series of (strict) updates on the initial value z.
  -- Because foldr is lazy, the value cl is only partially evaluated when it is (tail-recursively)
  -- applied to the strict value (cf zl x).
  cfl x cl zl = cl $! cf zl x
  ffl cl zl = cl $! ff zl

ambFoldR :: (AmbResult f Identity) => (t -> r -> r) -> (r -> r) -> r -> f t -> r
ambFoldR cf ff z ts = runIdentity $ ambFoldRT cf ff z ts

ambFoldL' :: (AmbResult f Identity) => (r -> t -> r) -> (r -> r) -> r -> f t -> r
ambFoldL' cf ff z ts = runIdentity $ ambFoldLT' cf ff z ts

newtype ChurchFoldable t = ChurchFoldable (forall r. (t -> r -> r) -> r -> r)

asFoldable :: (AmbResult a Identity) => a t -> ChurchFoldable t
asFoldable a = ChurchFoldable $ \f z -> runIdentity $ ambFoldRT f id z a

instance Foldable ChurchFoldable where
  foldr fn z (ChurchFoldable f) = f fn z

asMaybeFoldable :: (AmbResult a Identity) => a t -> ChurchFoldable (Maybe t)
asMaybeFoldable a = ChurchFoldable $ \f z -> runIdentity $ ambFoldRT (f . Just) (f Nothing) z a

ambEq :: (AmbResult a Identity, AmbResult b Identity, Eq t) => a t -> b t -> Bool
ambEq as bs = toList (asMaybeFoldable as) == toList (asMaybeFoldable bs)

ambShow :: (AmbResult a Identity, Show t) => String -> a t -> String
ambShow name as = name ++ "[" ++ (show . toList $ asMaybeFoldable as) ++ "]"

-- TODO: foldable
-- TODO invent some invariants for Amb as a transformer
-- Amb laws: join (amb <$> fs) == amb (join fs) where fs is a list of Foldables.
-- When a is a monad transformer, the transformed monad must be sequenced depth-first. TODO: test.
class Monad a => Amb a where
  -- The reason we use [], instead of the more general Foldable, is because amb must be strict in the LHS but not
  -- the RHS of the fold. The [] functor encapsulates this naturally.
  amb :: [t] -> a t
  -- t is, of course, unused here
  -- TODO: need to write some failure laws and test fail.
  afail :: a t

ambMaybe :: Amb a => [Maybe t] -> a t
ambMaybe mts = join . amb $ f <$> mts where
  f (Just x) = return x
  f Nothing = afail

-- TODO: class Amb a => AmbM a?
class Amb a => Logic a where
  split :: a t -> a (a t)

-- TODO: This is the Church amb, which should be the fastest Amb. Test it.
-- We put m r everywhere so ChurchAmbT never has to use the underlying bind.
-- We need m in the ChurchAmb type so we can make it a monad transformer later.
-- As a bonus, no property of t, m or r is used 'behind' the forall, so any bind/return/&c takes place
-- in the destructor, which improves inlining in the usual case.
newtype ChurchAmbT m t = ChurchAmbT { runChurchAmbT :: forall r. (t -> m r -> m r) -> (m r -> m r) -> m r -> m r }

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
  afail = ChurchAmbT $ \_ f z -> f z

instance MonadTrans ChurchAmbT where
  -- The only time we use m as a monad.
  lift mx = ChurchAmbT $ \c _ z -> mx >>= \x -> c x z

instance Monad m => AmbResult (ChurchAmbT m) m where
  type Target (ChurchAmbT m) = m
  ambFoldRT cf ff z xs = runChurchAmbT xs (fmap . cf) (fmap ff) (return z)

instance Eq a => Eq (ChurchAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ChurchAmbT Identity a) where
  show = ambShow "ChurchAmb"

-- ScottAmb is in some respects an asymptotic improvement over ChurchAmb. The reducing function, instead of being a fold,
-- gets a (first, rest) representation of the amb, which yields O(n) access to n elements. But:
-- * All operations are slower, because constructing the tail of a ScottAmb is expensive.
-- * Binds multiply all operations by a constant factor of O(n).
-- As a consequence, prepends are O(n) in the number of prepended elements.
newtype ScottAmbT m t = ScottAmbT {
  runScottAmbT :: forall r. (t -> ScottAmbT m t -> m r) -> (ScottAmbT m t -> m r) -> m r -> m r
}

type ScottAmb = ScottAmbT Identity

instance Functor (ScottAmbT f) where
  -- Need to define fmap because we use it in >>=
  fmap f xs = ScottAmbT $ \cy fy z -> let
    cx x xs1 = cy (f x) $ f <$> xs1
    fx xs1 = fy $ f <$> xs1
    in runScottAmbT xs cx fx z

instance Applicative (ScottAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ScottAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  xs >>= fxys = scottJoin $ fxys <$> xs where
    scottJoin xss0 = ScottAmbT $ \c0 f0 z0 -> let
      cxs xs0 xss = let cx x xs1 = c0 x $ combine xs1 xss
                        fx xs1 = f0 $ combine xs1 xss
                        zx = runScottAmbT xss cxs fxs z0
                        combine a as = scottJoin $ ScottAmbT $ \ca _ _ -> ca a as
                    in runScottAmbT xs0 cx fx zx
      fxs xss = f0 $ scottJoin xss
      in runScottAmbT xss0 cxs fxs z0

instance Amb (ScottAmbT m) where
  amb [] = ScottAmbT $ \_ _ z -> z
  amb (x:xs) = ScottAmbT $ \c _ _ -> c x $ amb xs
  afail = ScottAmbT $ \_ f _ -> f $ amb []

instance MonadTrans ScottAmbT where
  -- The only time we use m as a monad.
  lift mx = ScottAmbT $ \c _ _ -> mx >>= \x -> c x $ amb []

instance Monad m => AmbResult (ScottAmbT m) m where
  type Target (ScottAmbT m) = m
  ambFoldRT cf ff z xs = runScottAmbT xs cf1 ff1 (return z) where
    cf1 first rest = cf first <$> ambFoldRT cf ff z rest
    ff1 = ambFoldRT cf ff z

instance Eq a => Eq (ScottAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ScottAmbT Identity a) where
  show = ambShow "ScottAmb"

-- The best of both worlds--most operations are simple folds, but we always pass in a (lazy) tail
-- in case we need it. The efficiency of a Church list with an O(1) tail operation.
newtype ParigotAmbT m t = ParigotAmbT {
  runParigotAmbT :: forall r. (t -> ParigotAmbT m t -> m r -> m r) -> (ParigotAmbT m t -> m r -> m r) -> m r -> m r
}

type ParigotAmb = ParigotAmbT Identity

instance Functor (ParigotAmbT f) where
  fmap = liftM

instance Applicative (ParigotAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ParigotAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  xs >>= fxys = ParigotAmbT $ \cy fy z0 -> let
    cx x xs1 = runParigotAmbT (fxys x) cy fy
    fx xs1 = fy (xs >>= fxys)
    in runParigotAmbT xs cx fx z0

instance Amb (ParigotAmbT m) where
  amb [] = ParigotAmbT $ \_ _ z -> z
  amb (x:xs) = ParigotAmbT $ \c _ z -> c x axs $ runParigotAmbT axs c undefined z where axs = amb xs
  afail = ParigotAmbT $ \_ f z -> f (amb []) z

instance MonadTrans ParigotAmbT where
  -- The only time we use m as a monad.
  lift mx = ParigotAmbT $ \c _ z -> mx >>= \x -> c x (amb []) z

instance Monad m => AmbResult (ParigotAmbT m) m where
  type Target (ParigotAmbT m) = m
  ambFoldRT cf ff z xs =
    -- Here we see the advantage of laziness: _rest is never used.
    runParigotAmbT xs (\first _rest accumrm -> cf first <$> accumrm) (\_rest accumrm -> ff <$> accumrm) (return z)

instance Eq a => Eq (ParigotAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ParigotAmbT Identity a) where
  show = ambShow "ScottAmb"
