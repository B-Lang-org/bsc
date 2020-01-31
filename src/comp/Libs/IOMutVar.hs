module IOMutVar(MutableVar, newVar, readVar, writeVar) where

import Data.IORef

type MutableVar a = IORef a

newVar = newIORef
readVar = readIORef
writeVar = writeIORef
