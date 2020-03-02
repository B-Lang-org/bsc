{-# LANGUAGE CPP #-}
module IOUtil(progArgs, getEnvDef) where

import System.Environment(getArgs,getEnv)
import System.IO.Unsafe
import qualified Control.Exception as CE

{-# NOINLINE progArgs #-}
progArgs :: [String]
progArgs = unsafePerformIO $ do
  args <- getArgs
  bscopts <- getEnvDef "BSC_OPTIONS" ""
  return $ (words bscopts) ++ args

getEnvDef :: String -> String -> IO String
getEnvDef e d = CE.catch (getEnv e) handler
  where
    handler :: CE.SomeException -> IO String
    handler _ = return d
