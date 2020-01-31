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
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 611)
import GHC.IO(IO(..))
import GHC.MVar(MVar(..))
#else
import GHC.IOBase(IO(..), MVar(..))
#endif
import GHC.Exts(putMVar#, tryPutMVar#)

import qualified Control.Exception as CE

-- Instead of rnf, use hyper
--import Control.DeepSeq
import Eval

-- hack around base-3 and base-4 incompatibility
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 609)
#define NEW_EXCEPTION_API
#endif

-- block/unblock were deprecated in GHC 7
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 700)
#define HAS_EXCEPTION_MASK
#endif

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
putMVar  :: Hyper a => MVar a -> a -> IO ()
putMVar (MVar mvar#) !x = hyper x `seq` IO $ \ s# -> -- strict!
    case putMVar# mvar# x s# of
        s2# -> (# s2#, () #)

-- | A non-blocking version of 'putMVar'.  The 'tryPutMVar' function
-- attempts to put the value @a@ into the 'MVar', returning 'True' if
-- it was successful, or 'False' otherwise.
--
tryPutMVar  :: Hyper a => MVar a -> a -> IO Bool
tryPutMVar (MVar mvar#) !x = IO $ \ s# -> -- strict!
    case tryPutMVar# mvar# x s# of
        (# s, 0# #) -> (# s, False #)
        (# s, _  #) -> (# s, True #)

-- |Create an 'MVar' which contains the supplied value.
newMVar :: Hyper a => a -> IO (MVar a)
newMVar value =
    newEmptyMVar        >>= \ mvar ->
    putMVar mvar value  >>
    return mvar

{-|
  This is a combination of 'takeMVar' and 'putMVar'; ie. it takes the value
  from the 'MVar', puts it back, and also returns it.
-}
readMVar :: Hyper a => MVar a -> IO a
readMVar m =
#ifdef HAS_EXCEPTION_MASK
  CE.mask_ $ do
#else
  CE.block $ do
#endif
    a <- takeMVar m
    putMVar m a
    return a

{-|
  Take a value from an 'MVar', put a new value into the 'MVar' and
  return the value taken. Note that there is a race condition whereby
  another process can put something in the 'MVar' after the take
  happens but before the put does.
-}
swapMVar :: Hyper a => MVar a -> a -> IO a
swapMVar mvar new =
#ifdef HAS_EXCEPTION_MASK
  CE.mask_ $ do
#else
  CE.block $ do
#endif
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
withMVar :: Hyper a => MVar a -> (a -> IO b) -> IO b
withMVar m io =
#ifdef HAS_EXCEPTION_MASK
  CE.mask $ \ restore -> do
#else
  CE.block $ do
    let restore = CE.unblock
#endif
    a <- takeMVar m
    let
#ifdef NEW_EXCEPTION_API
        handler :: CE.SomeException -> IO b
#else
        handler :: CE.Exception -> IO b
#endif
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
modifyMVar_ :: Hyper a => MVar a -> (a -> IO a) -> IO ()
modifyMVar_ m io =
#ifdef HAS_EXCEPTION_MASK
  CE.mask $ \ restore -> do
#else
  CE.block $ do
    let restore = CE.unblock
#endif
    a  <- takeMVar m
    let
#ifdef NEW_EXCEPTION_API
        handler :: CE.SomeException -> IO b
#else
        handler :: CE.Exception -> IO b
#endif
        handler e = do putMVar m a
                       CE.throw e
    a' <- CE.catch (restore (io a)) handler
    putMVar m a'

{-|
  A slight variation on 'modifyMVar_' that allows a value to be
  returned (@b@) in addition to the modified value of the 'MVar'.
-}
{-# INLINE modifyMVar #-}
modifyMVar :: Hyper a => MVar a -> (a -> IO (a,b)) -> IO b
modifyMVar m io =
#ifdef HAS_EXCEPTION_MASK
  CE.mask $ \ restore -> do
#else
  CE.block $ do
    let restore = CE.unblock
#endif
    a      <- takeMVar m
    let
#ifdef NEW_EXCEPTION_API
        handler :: CE.SomeException -> IO b
#else
        handler :: CE.Exception -> IO b
#endif
        handler e = do putMVar m a
                       CE.throw e
    (a',b) <- CE.catch (restore (io a)) handler
    putMVar m a'
    return b

