{-# LANGUAGE CPP #-}
module IOUtil(progArgs, getEnvDef) where

import System.Environment(getArgs,getEnv)
import System.IO.Unsafe
import qualified Control.Exception as CE

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 609)
type ExceptionType = CE.SomeException
#else
type ExceptionType = CE.Exception
#endif


{-# NOINLINE progArgs #-}
progArgs :: [String]
progArgs = unsafePerformIO $ do
  args <- getArgs
  bscopts <- getEnvDef "BSC_OPTIONS" ""
  return $ (words bscopts) ++ args

getEnvDef :: String -> String -> IO String
getEnvDef e d = CE.catch (getEnv e) handler
  where
    handler :: ExceptionType -> IO String
    handler _ = return d

