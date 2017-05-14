module Tests where

import Distribution.TestSuite.QuickCheck

import Control.Logic.Test.Amb

tests :: IO [Test]
tests = return [ambTests]
