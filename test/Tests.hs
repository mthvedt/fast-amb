module Tests where

import Distribution.TestSuite.QuickCheck

import Control.Logic.Amb.Test

tests :: IO [Test]
tests = return [ambTests]
