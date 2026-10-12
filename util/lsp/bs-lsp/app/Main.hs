-- | Main entry point for the Bluespec LSP server.
module Main (main) where

import System.Exit (exitWith, ExitCode(..))

import Language.Bluespec.LSP.Server (runServer)

main :: IO ()
main = do
  exitCode <- runServer
  exitWith $ if exitCode == 0 then ExitSuccess else ExitFailure exitCode
