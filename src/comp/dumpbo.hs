{-# LANGUAGE CPP #-}
module Main_dumpbo(main) where

-- GHC 6.12 and beyond honor the default character encoding
-- based on the current locale.  We have to set it explicitly
-- to Latin1 for backward compatibility.
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 611)
#define SET_LATIN1_ENCODING
#endif

import System.Environment(getArgs)
import System.Exit(exitWith, ExitCode(..))

import PPrint
import GenBin
import BinaryIO
import ISyntax
import Error(initErrorHandle)

#ifdef SET_LATIN1_ENCODING
import System.IO
#endif

main = do
    errh <- initErrorHandle
    as <- getArgs
    (isBI, fname) <- case as of
                       ["-bi", mi]             -> return (True, mi)
                       [mi@(c:_)] | (c /= '-') -> return (False, mi)
                       _ -> do putStr ("Usage: dumpbo [-bi] mod-id\n")
                               exitWith (ExitFailure 1)
    file <- readBinaryFile fname
    (bi_sig, bo_sig, ipkg, hash) <- readBinFile errh fname file
#ifdef SET_LATIN1_ENCODING
    hSetEncoding stdout latin1
#endif
    if (isBI)
       then do putStr (ppReadable bi_sig)
       else do putStrLn ("Internal Symbols (export): ")
               putStr (ppReadable bi_sig)
               putStrLn ("Internal Symbols (all): ")
               putStr (ppReadable bo_sig)
               putStr (ppReadable (ipkg :: IPackage ()))
               putStrLn ("Hash: " ++ hash)
    exitWith ExitSuccess
