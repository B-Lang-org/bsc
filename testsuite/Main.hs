{-# LANGUAGE BangPatterns, CPP #-}
module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "BSC Tests"
  [ testGroup "Unit Tests"
      [ testCase "Basic Compilation" $ do
          -- Test that bsc can compile a simple file
          True @=? True  -- Placeholder test
      ]
  , testGroup "Property Tests"
      [ testProperty "Simple Property" $ \x ->
          (x :: Int) + 0 == x  -- Placeholder property test
      ]
  ] 