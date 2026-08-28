module IOMutVar(MutableVar, newVar, readVar, writeVar) where

import Data.IORef

type MutableVar a = IORef a

newVar :: a -> IO (MutableVar a)
newVar = newIORef

readVar :: MutableVar a -> IO a
readVar = readIORef

writeVar :: MutableVar a -> a -> IO ()
writeVar = writeIORef 