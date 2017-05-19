{-# LANGUAGE
  FlexibleContexts,
  ScopedTypeVariables
#-}

module Main where

import Control.Monad
import Control.Monad.Identity

import Control.DeepSeq
import Control.Monad.Random

import Control.Logic.Amb

import Criterion.Main

{-# ANN module "HLint: ignore Reduce duplication" #-}

nestedAmbs :: (RandomGen g, Amb a) => Int -> Int -> Rand g (a Int)
nestedAmbs s d | d <= 0 = error "depth must be > 0"
nestedAmbs s d | s <= 0 = error "size must be > 0"
nestedAmbs s 1 = amb . force <$> replicateM s getRandom
nestedAmbs s d = ambcat <$> replicateM s (nestedAmbs s (d - 1))

sumAmb :: AmbFold Identity a => a Int -> Int
sumAmb = ambFoldL' (+) id 0

depth2Inline :: (RandomGen g, Amb a) => Rand g (a Int)
depth2Inline = do
  ints <- replicateM 256 getRandom
  let aints = amb ints
  return $ do
    i <- aints
    j' <- aints
    let j = i + j'
    return (i + j)

depth4Inline :: (RandomGen g, Amb a) => Rand g (a Int)
depth4Inline = do
  ints <- replicateM 16 getRandom
  let aints = amb ints
  return $ do
    a <- aints
    b' <- aints
    let b = a + b'
    c' <- aints
    let c = b + c'
    d <- aints
    return (c + d)

depth8Inline :: (RandomGen g, Amb a) => Rand g (a Int)
depth8Inline = do
  ints <- replicateM 4 getRandom
  let aints = amb ints
  return $ do
    a <- aints
    b' <- aints
    let b = a + b'
    c' <- aints
    let c = b + c'
    d' <- aints
    let d = c + d'
    e' <- aints
    let e = d + e'
    f' <- aints
    let f = e + f'
    g' <- aints
    let g = f + g'
    h <- aints
    return (g + h)

depth16Inline :: (RandomGen g, Amb a) => Rand g (a Int)
depth16Inline = do
  ints <- replicateM 2 getRandom
  let aints = amb ints
  return $ do
    a0 <- aints
    a1' <- aints
    let a1 = a0 + a1'
    a2' <- aints
    let a2 = a1 + a2'
    a3' <- aints
    let a3 = a2 + a3'
    a4' <- aints
    let a4 = a3 + a4'
    a5' <- aints
    let a5 = a4 + a5'
    a6' <- aints
    let a6 = a5 + a6'
    a7' <- aints
    let a7 = a6 + a7'
    a8' <- aints
    let a8 = a7 + a8'
    a9' <- aints
    let a9 = a8 + a9'
    aa' <- aints
    let aa = a9 + aa'
    ab' <- aints
    let ab = aa + ab'
    ac' <- aints
    let ac = ab + ac'
    ad' <- aints
    let ad = ac + ad'
    ae' <- aints
    let ae = ad + ae'
    af <- aints
    return (ae + af)

benchAmb :: (RandomGen g, Amb a, AmbFold Identity a) => String -> a Int -> Rand g Benchmark
benchAmb s (_w :: a Int) = bgroup s <$> sequence
  [ sumBenchNested "2^16, flat" 65536 1
  , sumBenchNested "2^16, depth 2" 256 2
  , sumBenchNested "2^16, depth 4" 16 4
  , sumBenchNested "2^16, depth 8" 4 8
  , sumBenchNested "2^16, depth 16" 2 16
  , sumBench "2^16, depth 2, inline" depth2Inline
  , sumBench "2^16, depth 4, inline" depth4Inline
  , sumBench "2^16, depth 8, inline" depth8Inline
  , sumBench "2^16, depth 16, inline" depth16Inline
  ] where
    sumBench :: RandomGen g => String -> Rand g (a Int) -> Rand g Benchmark
    sumBench str ints = bench str . nf sumAmb <$> ints
    sumBenchNested str s d = sumBench str $ nestedAmbs s d

main = defaultMain . evalRand (sequence b) $ mkStdGen 0 where
  b = [ benchAmb "ChurchAmb" (return 1 :: ChurchAmb Int)
      , benchAmb "ScottAmb" (return 1 :: ScottAmb Int)
      , benchAmb "ParigotAmb" (return 1 :: ParigotAmb Int)
      , benchAmb "FastAmb" (return 1 :: FastAmb Int)
      ]
