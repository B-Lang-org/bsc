module IOMutVar(MutableVar, newVar, readVar, writeVar) where

import Data.IORef

type MutableVar a = IORef a

newVar :: a -> IO (IORef a)
newVar = newIORef

readVar :: IORef a -> IO a
readVar = readIORef

writeVar :: IORef a -> a -> IO ()
writeVar = writeIORef
