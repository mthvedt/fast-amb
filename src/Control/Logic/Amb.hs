{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  FunctionalDependencies,
  MultiParamTypeClasses,
  RankNTypes,
  TypeFamilies
#-}

-- Continuation-passing implementation of Amb.
-- Inspired by https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf.

module Control.Logic.Amb where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Foldable (toList)

class (Amb a, Monad m) => AmbFold m a | a -> m where
  ambFoldRT :: (t -> m r -> m r) -> m r -> a t -> m r

-- TODO test all of these
ambFoldLT' :: AmbFold m a => (m r -> t -> m r) -> m r -> a t -> m r
{-# INLINABLE ambFoldLT' #-}
ambFoldLT' c0 mz xs = unwrap $ ambFoldRT mc (return id) xs where
  -- This transforms a list into a series of (strict) updates on the initial value z.
  -- We note that the function cont, of type m r -> m r, is finitely bounded because foldr is lazy.
  -- So a foldr is turned into a strict foldl in finite space.
  -- c :: t -> (m r -> m r) -> m r -> m r
  c x cont acc = cont $! c0 acc x
  -- mc :: t -> m (m r -> m r) -> m (m r -> m r)
  mc x mcont = c x <$> mcont
  -- unwrap :: m (m r -> m r) -> m r
  unwrap zl = join $ (\f -> f mz) <$> zl

ambFoldRM :: AmbFold m a => (t -> r -> m r) -> r -> a t -> m r
{-# INLINABLE ambFoldRM #-}
ambFoldRM c0 z = ambFoldRT c (return z) where
  c x mr = mr >>= c0 x

ambFoldLM' :: AmbFold m a => (r -> t -> m r) -> r -> a t -> m r
ambFoldLM' c0 z = ambFoldLT' c (return z) where
  c mr x = mr >>= \r -> c0 r x

ambFoldR :: AmbFold Identity a => (t -> r -> r) -> r -> a t -> r
{-# INLINABLE ambFoldR #-}
ambFoldR c z a = runIdentity $ ambFoldRM (\t r -> return $ c t r) z a

ambFoldL' :: AmbFold Identity a => (r -> t -> r) -> r -> a t -> r
{-# INLINABLE ambFoldL' #-}
ambFoldL' c z a = runIdentity $ ambFoldLM' (\r t -> return $ c r t) z a

-- TODO what's this for?
newtype ChurchFoldable t = ChurchFoldable (forall r. (t -> r -> r) -> r -> r)

instance Foldable ChurchFoldable where
  {-# INLINABLE foldr #-}
  foldr c z (ChurchFoldable f) = f c z

asFoldable :: AmbFold Identity a => a t -> ChurchFoldable t
{-# INLINABLE asFoldable #-}
asFoldable a = ChurchFoldable $ \f z -> ambFoldR f z a

ambEq :: (AmbFold Identity a, AmbFold Identity b, Eq t) => a t -> b t -> Bool
{-# INLINABLE ambEq #-}
ambEq as bs = toList (asFoldable as) == toList (asFoldable bs)

ambShow :: (AmbFold Identity a, Show t) => String -> a t -> String
{-# INLINABLE ambShow #-}
ambShow name as = name ++ (show . toList $ asFoldable as)

-- Amb laws:
-- Let [[as]] be a list of list of ambs. Then
-- ambcat (ambcat <$> as) === join (ambcat <$> amb as), where ambcat = join . amb.
class Monad a => Amb a where
  -- Creates an Amb which returns the given elements in order, never failing.
  --
  -- Ambs are often split into (first, rest) pairs, and list is the simplest functor
  -- that does this performantly. This is why the amb function operates on a list,
  -- instead of the more general Foldable.
  amb :: [t] -> a t

ambzero :: Amb a => a t
{-# INLINABLE ambzero #-}
ambzero = amb []

ambcat :: Amb a => [a t] -> a t
{-# INLINABLE ambcat #-}
ambcat = join . amb

toListM :: AmbFold m a => a t -> m [t]
{-# INLINABLE toListM #-}
toListM = ambFoldRT (\x xs -> (x:) <$> xs) $ return []

-- ambcons :: Amb a => t -> a t -> a t
-- ambcons x xs = ambcat [return x, xs]

-- An AmbTrans is a monad transformer obeying the Amb and AmbTrans laws, viz:
-- join . amb $ amblift <$> ms === amblift (join ms) where ms is of type [[m x]].
-- TODO need to be able to mix with regular amb.
-- TODO: maybe use MFunctor instead, or together with this.
class (MonadTrans t, Monad m, Amb (t m), AmbFold m (t m)) => AmbTrans t m where

amblift :: AmbTrans t m => [m a] -> t m a
{-# INLINABLE amblift #-}
amblift ms = join . amb $ lift <$> ms

-- An AmbLogic is an Amb that supports uncons: getting a first and a rest.
-- Minimal complete definition: ambuncons | ambpeek.
-- Must obey the following laws:
-- TODO: express these laws in terms of observeMany
-- * ambpeek f a === ambuncons a >>= uncurry f,
-- * ambuncons $ amb as === amb (return $ first as, amb $ rest as) when as is non-empty,
-- * ambuncons $ amb as === ambzero when as is empty.
-- In particular,
-- * let Amb a => (x, y), where x converges and is nonempty, and y diverges.
-- Then ambuncons $ ambcat [x, y] should not diverge when evaluated.
-- * If a is a monad transformer, a should not behave like ListT where
-- the entire list of monadic values is always evaluated.
class Amb a => AmbLogic a where
  ambpeek :: (t -> a t -> a r) -> a t -> a r
  {-# INLINABLE ambpeek #-}
  ambpeek f a = ambuncons a >>= uncurry f
  ambuncons :: a t -> a (t, a t)
  {-# INLINABLE ambuncons #-}
  ambuncons = ambpeek $ curry return

-- TODO
-- observe :: AmbLogic a => a t -> a t
-- observe xs = fst <$> ambuncons xs

-- TODO
observeMany :: AmbLogic a => Int -> a t -> a ([t], a t)
{-# INLINABLE observeMany #-}
observeMany x _ | x < 0 = error "cannot observe less than 0"
observeMany 0 xs = return ([], xs)
-- Need to do this ambcat so if xs0 is empty, we still get []
observeMany i xs0 = ambcat [r, return ([], ambzero)] where
  f x tail0 = do
    (xs, tail1) <- observeMany (i - 1) tail0
    return (x:xs, tail1)
  r = ambpeek f xs0

-- -- TODO: testme
-- -- TODO: class or func?
-- class (Monad (MorphSrc f), Monad (MorphDest f)) => MonadMorph f where
--   type MorphSrc f :: * -> *
--   type MorphDest f :: * -> *
--   morphM :: f -> (MorphSrc f) x -> (MorphDest f) x
--
-- newtype MorphMBox m n = MorphMBox (forall x. m x -> n x)
--
-- instance (Monad m, Monad n) => MonadMorph (MorphMBox m n) where
--   type MorphSrc (MorphMBox m n) = m
--   type MorphDest (MorphMBox m n) = n
--   morphM (MorphMBox f) = f
--
-- asMorphM :: (forall x. m x -> n x) -> MorphMBox m n
-- asMorphM = MorphMBox

-- -- TODO use MFunctor instead
-- -- A MonadFunc is a functor on the category of monads. A {function, natural transformation, morphism of monads}
-- -- can be lifted into the MonadFunc.
-- -- fmapM must obey the functor laws:
-- -- fmapM id == id
-- -- fmapM (f . g) == fmap f . fmap g
-- -- and lift must be a map of functors (alternatively, lift itself is a natural endotransformation on monads)
-- -- obeying fmapM t . lift = lift . t
-- -- From this we can deduce that when f is a {function, natural transformation, monad morphism},
-- -- `fmapT f` is one also.
-- -- TODO: testme
-- class MonadTrans t => MonadFunc t where
--   fmapT :: (Monad m, Monad n) => (forall x. m x -> n x) -> t m v -> t n v

-- We put m r everywhere so ChurchAmbT never has to use the underlying bind.
-- We need m in the ChurchAmb type so we can make it a monad transformer later.
-- As a bonus, no property of t, m or r is used 'behind' the forall, so any bind/return/&c takes place
-- in the destructor.
newtype ChurchAmbT m t = ChurchAmbT { runChurchAmbT :: forall r. (t -> m r -> m r) -> m r -> m r }

type ChurchAmb = ChurchAmbT Identity

instance Functor (ChurchAmbT f) where
  fmap = liftM
  {-# INLINABLE fmap #-}

instance Applicative (ChurchAmbT a) where
  pure = return
  {-# INLINABLE pure #-}
  (<*>) = ap
  {-# INLINABLE (<*>) #-}

instance Monad (ChurchAmbT m) where
  return x = amb [x]
  {-# INLINABLE return #-}
  -- note that f is called for failures in both the lhs and the rhs.
  -- Also, because both the outer and inner runAmbs are right-associative, we have proper right-associativity
  -- which yields the laziness and O(n) asymptotics we need.
  -- TODO: test both above assertions.
  -- TODO: test the underlying binding is correct. It should be. See 'ListT done right' for test ideas.
  xs0 >>= fxys = ChurchAmbT $ \c z0 -> runChurchAmbT xs0 (\x z1 -> runChurchAmbT (fxys x) c z1) z0
  {-# INLINABLE (>>=) #-}

instance MonadTrans ChurchAmbT where
  -- The only time we use m as a monad.
  lift mx = ChurchAmbT $ \c z -> mx >>= \x -> c x z
  {-# INLINABLE lift #-}

instance Amb (ChurchAmbT m) where
  amb xs = ChurchAmbT $ \c z -> foldr c z xs
  {-# INLINABLE amb #-}

instance Monad m => AmbTrans ChurchAmbT m

-- instance MonadFunc ChurchAmbT where
--   fmapT n a = ChurchAmbT $ \c0 f0 z0 -> let
--     -- We run the original amb a with a return type m (n r),
--     -- then use join . nat to strip away the extra m.
--     -- c0 :: a -> n r -> n r. We need to make something of type a -> m (n r) -> m (n r)
--     c x mnz = c0 x <$> mnz
--     f mnz = f0 <$> mnz
--     z = return z0
--     in join . n $ runChurchAmbT a c f z

instance Monad m => AmbFold m (ChurchAmbT m) where
  ambFoldRT f z (ChurchAmbT inner) = inner f z
  {-# INLINABLE ambFoldRT #-}

instance Monad m => AmbLogic (ChurchAmbT m) where
  ambuncons a0 = join . lift $ runChurchAmbT a0 c0 z0 where
    -- The goal of c0 and f0 are to turn our original amb, a0, into an amb of type
    -- m (ChurchAmbT m (t, ChurchAmbT m t)), and then join it.
    -- c0, accepts a `t` and an `m (ChurchAmbT m (t, ChurchAmbT m t))` argument.
    -- Our goal is to convert those into `m (ChurchAmbT m (t, ChurchAmbT m t))`.
    c0 x msplitrest = return split where
      -- asplit :: ChurchAmbT m (t, ChurchAmbT m t)
      split = ChurchAmbT $ \csplit z -> csplit (x, rest) z where
        -- rest :: ChurchAmbT' m t, the rest of our original amb
        -- recall that splitrest is what happens when c0 is folded over the rest of our original amb.
        -- It is of type m (ChurchAmbT m (t, ChurchAmbT m t)).
        -- We need to turn it into a ChurchAmbT m t.
        rest = ChurchAmbT $ \c z' -> msplitrest >>= let
          unwrap splitrest = runChurchAmbT splitrest unsplit z'
          unsplit (x1, rest') _ = c x1 $ runChurchAmbT rest' c z'
          in unwrap
    z0 = return ambzero
  {-# INLINABLE ambuncons #-}

instance Show a => Show (ChurchAmbT Identity a) where
  show = ambShow "ChurchAmb"

-- ScottAmb is in some respects an asymptotic improvement over ChurchAmb. The reducing function, instead of being a fold,
-- gets a (first, rest) representation of the amb, which yields O(n) access to n elements. But:
-- * All operations are slower, because constructing the tail of a ScottAmb is expensive.
-- * Binds multiply all operations by a constant factor of O(n).
-- As a consequence, prepends are O(n) in the number of prepended elements.
newtype ScottAmbT m t = ScottAmbT {
  runScottAmbT :: forall r. (t -> ScottAmbT m t -> m r) -> m r -> m r
}

type ScottAmb = ScottAmbT Identity

instance Functor (ScottAmbT f) where
  -- Need to define fmap because we use it in >>=
  fmap f xs = ScottAmbT $ \cy z -> let
    cx x xs1 = cy (f x) $ f <$> xs1
    in runScottAmbT xs cx z

instance Applicative (ScottAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ScottAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  xs >>= fxys = scottJoin $ fxys <$> xs where
    scottJoin xss0 = ScottAmbT $ \c0 z0 -> let
      cxs xs0 xss = let cx x xs1 = c0 x . scottJoin $ ScottAmbT $ \ca _ -> ca xs1 xss
                        zx = runScottAmbT xss cxs z0
                    in runScottAmbT xs0 cx zx
      in runScottAmbT xss0 cxs z0

instance MonadTrans ScottAmbT where
  -- The only time we use m as a monad.
  lift mx = ScottAmbT $ \c _ -> mx >>= \x -> c x ambzero

instance Amb (ScottAmbT m) where
  amb [] = ScottAmbT $ \_ z -> z
  amb (x:xs) = ScottAmbT $ \c _ -> c x $ amb xs

-- TODO: test ambpeek
instance AmbLogic (ScottAmbT m) where
  ambpeek mf xs0 = ScottAmbT $ \cf0 z0 -> let
    cf x xs = runScottAmbT (mf x xs) cf0 z0
    in runScottAmbT xs0 cf z0

instance Monad m => AmbFold m (ScottAmbT m) where
  ambFoldRT cf mz xs = runScottAmbT xs cf1 mz where
    cf1 first rest = cf first $ ambFoldRT cf mz rest

-- TODO: soon won't need these
instance Eq a => Eq (ScottAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ScottAmbT Identity a) where
  show = ambShow "ScottAmb"

-- The best of both worlds--most operations are simple folds, but we always pass in a (lazy) tail
-- in case we need it. The efficiency of a Church list with an O(1) tail operation.
newtype ParigotAmbT m t = ParigotAmbT {
  runParigotAmbT :: forall r. (t -> ParigotAmbT m t -> m r -> m r) -> m r -> m r
}

type ParigotAmb = ParigotAmbT Identity

instance Functor (ParigotAmbT f) where
  -- Need to define fmap because we use it in >>=
  -- Note that though this looks similarly expensive to ScottAmb, in the case where fmap is inlined
  -- in the same context as the amb value xs,
  -- the expensive part is the boxing/unboxing terms `xs1` and `f <$> xs1`.
  -- In most Parigot folds neither are evaluated.
  fmap f xs = ParigotAmbT $ \cy z -> let
    cx x xs1 = cy (f x) $ f <$> xs1
    in runParigotAmbT xs cx z

instance Applicative (ParigotAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (ParigotAmbT m) where
  return x = amb [x]
  -- TODO: test laziness, asymptotics
  -- The expensive boxing/unboxing terms, here `combine`, are not usually evaluated.
  -- However, when not inlined, there is a layer of indirection executed once per element
  -- of the inner monad. Contrast to ChurchAmb where that
  -- layer is only executed once per element of the outer monad.
  xs >>= fxys = parigotJoin $ fxys <$> xs where
    parigotJoin yss0 = ParigotAmbT $ \cy z -> let
      cys ys0 yss = let cx y ys = cy y . parigotJoin $ ParigotAmbT $ \cw zw -> cw ys yss zw
                    in runParigotAmbT ys0 cy
      in runParigotAmbT yss0 cys z

instance MonadTrans ParigotAmbT where
  -- The only time we use m as a monad.
  lift mx = ParigotAmbT $ \c z -> mx >>= \x -> c x ambzero z

instance Amb (ParigotAmbT m) where
  amb [] = ParigotAmbT $ \_ z -> z
  amb (x:xs) = ParigotAmbT $ \c z -> c x axs $ runParigotAmbT axs c z where axs = amb xs

instance AmbLogic (ParigotAmbT m) where
  ambpeek mf xs0 = ParigotAmbT $ \cf0 z0 -> let
    cf x xs = runParigotAmbT (mf x xs) cf0
    in runParigotAmbT xs0 cf z0

instance Monad m => AmbFold m (ParigotAmbT m) where
  ambFoldRT cf z0 xs0 =
    -- Here we see the advantage of laziness: _xs is never used.
    runParigotAmbT xs0 (\x _xs z -> cf x z) z0

instance Eq a => Eq (ParigotAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (ParigotAmbT Identity a) where
  show = ambShow "ParigotAmb"

newtype FastAmbT m t = FastAmbT {
  runFastAmbT :: forall r. FastAmbT m t -> (t -> FastAmbT m t -> m r -> m r) -> m r -> m r
}

type FastAmb = FastAmbT Identity

instance Functor (FastAmbT f) where
  fmap = liftM

instance Applicative (FastAmbT a) where
  pure = return
  (<*>) = ap

instance Monad (FastAmbT m) where
  return x = amb [x]
  -- The crucial improvement here is that the inner runFastAmbT is executed directly on the continuations
  -- cy and fy.
  xs0 >>= fxys = FastAmbT $ \rest cy z0 -> let
    cx x xrest = runFastAmbT (fxys x) (ambcat [xrest >>= fxys, rest]) cy
    in runFastAmbT xs0 undefined cx z0

instance MonadTrans FastAmbT where
  -- The only time we use m as a monad.
  lift mx = FastAmbT $ \rest c z -> mx >>= \x -> c x rest z

instance Amb (FastAmbT m) where
  amb [] = FastAmbT $ \_ _ z -> z
  amb (x:xs) = FastAmbT $ \rest c z -> c x (ambcat [axs, rest]) $ runFastAmbT axs rest c z where
    axs = amb xs

instance AmbLogic (FastAmbT m) where
  ambpeek mf xs0 = FastAmbT $ \rest cf0 z0 -> let
    cf x xs = runFastAmbT (mf x xs) rest cf0
    in runFastAmbT xs0 undefined cf z0

instance Monad m => AmbFold m (FastAmbT m) where
  ambFoldRT cf z0 xs0 =
    -- Here we see the advantage of laziness: the _xs args are never used.
    runFastAmbT xs0 ambzero (\x _xs z -> cf x z) z0

instance Eq a => Eq (FastAmbT Identity a) where
  (==) = ambEq

instance Show a => Show (FastAmbT Identity a) where
  show = ambShow "FastAmb"
