{-# LANGUAGE CPP #-}

module TmpNam (tmpNam, localTmpNam) where

import System.Directory (getTemporaryDirectory)
import System.Process (getCurrentPid)

tmpNam :: IO String
tmpNam = do
    tmpDir <- getTemporaryDirectory -- Cross-platform temporary directory
    x <- localTmpNam
    return $ tmpDir ++ "/bsc" ++ x

localTmpNam :: IO String
localTmpNam = do
    x <- getCurrentPid
    return $ show x