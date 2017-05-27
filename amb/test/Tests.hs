module Tests where

import Distribution.TestSuite.QuickCheck

import Control.Monad.Logic.Amb.Test

tests :: IO [Test]
tests = return [ambTests]
