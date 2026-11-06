{-# LANGUAGE NoImplicitPrelude #-}
-- The launcher's own GHC statements must not depend on the script's scope.
module Main (main) where

import System.IO (IO, putStrLn)

main :: IO ()
main = putStrLn "no Prelude: ok"
