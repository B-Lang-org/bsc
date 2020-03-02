{-# LANGUAGE CPP #-}
module Exceptions (bsCatch) where

import qualified Control.Exception as CE
import Control.Monad(msum)
import System.IO.Error(ioeGetErrorString)
import System.IO(hFlush, stdout, hPutStr, stderr)
import System.Exit(ExitCode, exitFailure, exitWith)

bsCatch :: IO a -> IO a
bsCatch fn = CE.catch fn bscExceptions
        where bscExceptions :: CE.SomeException -> IO a
              bscExceptions e = let act = msum [ handleIOException e, handleErrorCall e, handleExit e]
                                in case act of
                                     (Just ioact) -> ioact
                                     Nothing      -> CE.throwIO e
              -- these are in the Maybe monad
              handleIOException ex =
                  do err <- (CE.fromException ex)::(Maybe CE.IOException)
                     let msg = (ioeGetErrorString err)
                     return $ hFlush stdout >> hPutStr stderr msg >> exitFailure
              handleErrorCall ex =
                  do (CE.ErrorCall msg) <- (CE.fromException ex)::(Maybe CE.ErrorCall)
                     return $ hFlush stdout >> hPutStr stderr msg >> exitFailure
              handleExit ex =
                  do exitcode <- (CE.fromException ex)::(Maybe ExitCode)
                     return $ exitWith exitcode
