{-# LANGUAGE CPP #-}
module Main_dumpba(main) where

import System.Environment(getArgs)

import BinaryIO
import GenABin
import PPrint
import Error(initErrorHandle)
import System.IO

main :: IO ()
main = do
    errh <- initErrorHandle
    as <- getArgs
    case as of
     [mi] -> do
        file <- readBinaryFile mi
        let (abi, hash) = readABinFile errh mi file
        hSetEncoding stdout latin1
        putStr (ppReadable abi)
        putStrLn ("Hash: " ++ hash)
     _ -> do
        putStr ("Usage: dumpba mod-id\n")
