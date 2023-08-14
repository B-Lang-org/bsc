{-# LANGUAGE CPP #-}
module Main_dumpba(main) where

import System.Environment(getArgs)

import GenABin
import PPrint
import Error(initErrorHandle)
import System.IO
import qualified Data.ByteString.Lazy as B

main :: IO ()
main = do
    errh <- initErrorHandle
    as <- getArgs
    case as of
     [mi] -> do
        file <- B.unpack <$> B.readFile mi
        let (abi, hash) = readABinFile errh mi file
        hSetEncoding stdout utf8
        putStr (ppReadable abi)
        putStrLn ("Hash: " ++ hash)
     _ -> do
        putStr ("Usage: dumpba mod-id\n")
