module Tests where

import Distribution.TestSuite.QuickCheck

import Test.Amb

tests :: IO [Test]
tests = return [ambTests]
