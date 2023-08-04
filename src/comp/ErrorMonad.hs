{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module ErrorMonad(ErrorMonad(..), convErrorMonadToIO) where

import Control.Monad(ap)
import Control.Monad.Except(MonadError, throwError, catchError)
#if !defined(__GLASGOW_HASKELL__) || ((__GLASGOW_HASKELL__ >= 800) && (__GLASGOW_HASKELL__ < 808))
import Control.Monad.Fail(MonadFail(..))
#endif
import Error(EMsg, WMsg, ErrMsg(..), ErrorHandle, bsError, bsWarning)
import Position(noPosition)

data ErrorMonad v = EMError [EMsg]
                  | EMWarning [WMsg] v
                  | EMResult v

instance Monad ErrorMonad where
    (EMError es) >>= _     = EMError es  -- XXX could merge errors
    (EMWarning ws v) >>= f = case f v of
                               EMError es       -> EMError es  -- XXX ws
                               EMWarning ws' v' -> EMWarning (ws ++ ws') v'
                               EMResult v'      -> EMWarning ws v'
    (EMResult v) >>= f     = (f v)
    return                 = pure
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 808)
    fail s                 = EMError [(noPosition, EGeneric s)]
#endif

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 800)
instance MonadFail ErrorMonad where
    fail s                 = EMError [(noPosition, EGeneric s)]
#endif

instance Functor ErrorMonad where
    fmap _ (EMError es)     = EMError es
    fmap f (EMWarning ws v) = EMWarning ws (f v)
    fmap f (EMResult v)     = EMResult (f v)

instance Applicative ErrorMonad where
  pure v = EMResult v
  (<*>) = ap

instance MonadError [EMsg] ErrorMonad where
    throwError es    = EMError es
    m `catchError` h = case m of
                         EMError es -> h es
                         _          -> m

convErrorMonadToIO :: ErrorHandle -> ErrorMonad a -> IO a
convErrorMonadToIO errh r =
    case r of
      EMError emsgs      -> bsError errh emsgs
      EMWarning wmsgs m' -> bsWarning errh wmsgs >> return m'
      EMResult m'        -> return m'
