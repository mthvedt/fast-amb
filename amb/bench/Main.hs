{-# LANGUAGE
  FlexibleContexts,
  ScopedTypeVariables
#-}

module Main where

import Control.Monad
import Control.Monad.Identity

import Control.DeepSeq
import Control.Monad.Logic
import Control.Monad.Random

import Control.Monad.Logic.Amb
import Control.Monad.Logic.Run

import Criterion.Main

{-# ANN module "HLint: ignore Reduce duplication" #-}

nestedLogic :: (RandomGen g, MonadLogic l) => Int -> Int -> Rand g (l Int)
nestedLogic s d | d <= 0 = error "depth must be > 0"
nestedLogic s d | s <= 0 = error "size must be > 0"
nestedLogic s 1 = (\x -> x `deepseq` amb x) <$> replicateM s getRandom
nestedLogic s d = ambcat <$> replicateM s (nestedLogic s (d - 1))

sumAmb :: RunLogic a => a Int -> Int
sumAmb = runLogicL' (+) 0

depth2Inline :: (RandomGen g, MonadLogic l) => Rand g (l Int)
depth2Inline = do
  ints <- replicateM 256 getRandom
  let aints = amb ints
  ints `deepseq` return $ do
    i <- aints
    j' <- aints
    let j = i + j'
    return (i + j)

depth4Inline :: (RandomGen g, MonadLogic l) => Rand g (l Int)
depth4Inline = do
  ints <- replicateM 16 getRandom
  let aints = amb ints
  ints `deepseq` return $ do
    a <- aints
    b' <- aints
    let b = a + b'
    c' <- aints
    let c = b + c'
    d <- aints
    return (c + d)

depth8Inline :: (RandomGen g, MonadLogic l) => Rand g (l Int)
depth8Inline = do
  ints <- replicateM 4 getRandom
  let aints = amb ints
  ints `deepseq` return $ do
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

depth16Inline :: (RandomGen g, MonadLogic l) => Rand g (l Int)
depth16Inline = do
  ints <- replicateM 2 getRandom
  let aints = amb ints
  ints `deepseq` return $ do
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

benchAmb :: (RandomGen g, MonadLogic l, RunLogic l) => String -> l Int -> Rand g Benchmark
benchAmb s (_w :: l Int) = bgroup s <$> sequence
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
    sumBench :: RandomGen g => String -> Rand g (l Int) -> Rand g Benchmark
    sumBench str ints = bench str . nf sumAmb <$> ints
    sumBenchNested str s d = sumBench str $ nestedLogic s d

main = defaultMain . evalRand (sequence b) $ mkStdGen 0 where
  b = [ benchAmb "List" []
      , benchAmb "Logic" (mzero :: Logic Int)
      , benchAmb "Amb" (mzero :: Amb Int)
      ]
