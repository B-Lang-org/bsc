{-# LANGUAGE CPP #-}
module Main_dumpba(main) where

-- GHC 6.12 and beyond honor the default character encoding
-- based on the current locale.  We have to set it explicitly
-- to Latin1 for backward compatibility.
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 611)
#define SET_LATIN1_ENCODING
#endif

import System.Environment(getArgs)

import BinaryIO
import GenABin
import PPrint
import Error(initErrorHandle)

#ifdef SET_LATIN1_ENCODING
import System.IO
#endif

main = do
    errh <- initErrorHandle
    as <- getArgs
    case as of
     [mi] -> do
        file <- readBinaryFile mi
        let (abi, hash) = readABinFile errh mi file
#ifdef SET_LATIN1_ENCODING
        hSetEncoding stdout latin1
#endif
        putStr (ppReadable abi)
        putStrLn ("Hash: " ++ hash)
     _ -> do
        putStr ("Usage: dumpba mod-id\n")
