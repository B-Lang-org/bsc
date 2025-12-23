{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- Adapted from
--
-- Module      :  Control.Concurrent.MVar.Strict
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (concurrency)
--
-- Synchronising, strict variables
--
-- Values placed in an MVar are evaluated to head normal form
-- before being placed in the MVar, preventing a common source of
-- space-leaks involving synchronising variables.
--
-----------------------------------------------------------------------------

module MVarStrict
        (
          -- * @MVar@s
          MVar          -- abstract
        , newEmptyMVar  -- :: IO (MVar a)
        , newMVar       -- :: a -> IO (MVar a)
        , takeMVar      -- :: MVar a -> IO a
        , putMVar       -- :: MVar a -> a -> IO ()
        , readMVar      -- :: MVar a -> IO a
        , swapMVar      -- :: MVar a -> a -> IO a
        , tryTakeMVar   -- :: MVar a -> IO (Maybe a)
        , tryPutMVar    -- :: MVar a -> a -> IO Bool
        , isEmptyMVar   -- :: MVar a -> IO Bool
        , withMVar      -- :: MVar a -> (a -> IO b) -> IO b
        , modifyMVar_   -- :: MVar a -> (a -> IO a) -> IO ()
        , modifyMVar    -- :: MVar a -> (a -> IO (a,b)) -> IO b
        , addMVarFinalizer -- :: MVar a -> IO () -> IO ()
    ) where

import Control.Concurrent.MVar(newEmptyMVar, takeMVar,
                               tryTakeMVar, isEmptyMVar, addMVarFinalizer)
import GHC.IO(IO(..))
import GHC.MVar(MVar(..))
import GHC.Exts(putMVar#, tryPutMVar#)

import qualified Control.Exception as CE

-- Instead of rnf, use hyper
--import Control.DeepSeq
import Eval

-- |Put a value into an 'MVar'.  If the 'MVar' is currently full,
-- 'putMVar' will wait until it becomes empty.
--
-- There are two further important properties of 'putMVar':
--
--   * 'putMVar' is single-wakeup.  That is, if there are multiple
--     threads blocked in 'putMVar', and the 'MVar' becomes empty,
--     only one thread will be woken up.  The runtime guarantees that
--     the woken thread completes its 'putMVar' operation.
--
--   * When multiple threads are blocked on an 'MVar', they are
--     woken up in FIFO order.  This is useful for providing
--     fairness properties of abstractions built using 'MVar's.
--
putMVar  :: NFData a => MVar a -> a -> IO ()
putMVar (MVar mvar#) !x = rnf x `seq` IO $ \ s# -> -- strict!
    case putMVar# mvar# x s# of
        s2# -> (# s2#, () #)

-- | A non-blocking version of 'putMVar'.  The 'tryPutMVar' function
-- attempts to put the value @a@ into the 'MVar', returning 'True' if
-- it was successful, or 'False' otherwise.
--
tryPutMVar  :: NFData a => MVar a -> a -> IO Bool
tryPutMVar (MVar mvar#) !x = IO $ \ s# -> -- strict!
    case tryPutMVar# mvar# x s# of
        (# s, 0# #) -> (# s, False #)
        (# s, _  #) -> (# s, True #)

-- |Create an 'MVar' which contains the supplied value.
newMVar :: NFData a => a -> IO (MVar a)
newMVar value =
    newEmptyMVar        >>= \ mvar ->
    putMVar mvar value  >>
    return mvar

{-|
  This is a combination of 'takeMVar' and 'putMVar'; ie. it takes the value
  from the 'MVar', puts it back, and also returns it.
-}
readMVar :: NFData a => MVar a -> IO a
readMVar m =
  CE.mask_ $ do
    a <- takeMVar m
    putMVar m a
    return a

{-|
  Take a value from an 'MVar', put a new value into the 'MVar' and
  return the value taken. Note that there is a race condition whereby
  another process can put something in the 'MVar' after the take
  happens but before the put does.
-}
swapMVar :: NFData a => MVar a -> a -> IO a
swapMVar mvar new =
  CE.mask_ $ do
    old <- takeMVar mvar
    putMVar mvar new
    return old

{-|
  'withMVar' is a safe wrapper for operating on the contents of an
  'MVar'.  This operation is exception-safe: it will replace the
  original contents of the 'MVar' if an exception is raised (see
  "Control.Exception").
-}
{-# INLINE withMVar #-}
-- inlining has been reported to have dramatic effects; see
-- http://www.haskell.org//pipermail/haskell/2006-May/017907.html
withMVar :: NFData a => MVar a -> (a -> IO b) -> IO b
withMVar m io =
  CE.mask $ \ restore -> do
    a <- takeMVar m
    let
        handler :: CE.SomeException -> IO b
        handler e = do putMVar m a
                       CE.throw e
    b <- CE.catch (restore (io a)) handler
    putMVar m a
    return b

{-|
  A safe wrapper for modifying the contents of an 'MVar'.  Like 'withMVar',
  'modifyMVar' will replace the original contents of the 'MVar' if an
  exception is raised during the operation.
-}
{-# INLINE modifyMVar_ #-}
modifyMVar_ :: NFData a => MVar a -> (a -> IO a) -> IO ()
modifyMVar_ m io =
  CE.mask $ \ restore -> do
    a  <- takeMVar m
    let
        handler :: CE.SomeException -> IO b
        handler e = do putMVar m a
                       CE.throw e
    a' <- CE.catch (restore (io a)) handler
    putMVar m a'

{-|
  A slight variation on 'modifyMVar_' that allows a value to be
  returned (@b@) in addition to the modified value of the 'MVar'.
-}
{-# INLINE modifyMVar #-}
modifyMVar :: NFData a => MVar a -> (a -> IO (a,b)) -> IO b
modifyMVar m io =
  CE.mask $ \ restore -> do
    a      <- takeMVar m
    let
        handler :: CE.SomeException -> IO b
        handler e = do putMVar m a
                       CE.throw e
    (a',b) <- CE.catch (restore (io a)) handler
    putMVar m a'
    return b
