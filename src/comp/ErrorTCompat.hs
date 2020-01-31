{-# LANGUAGE CPP #-}
module ErrorTCompat (
       ErrorT,
       runErrorT,
       MonadError(..),
       lift
) where

-- GHC 7.10.1 switched to 'transformers' 0.4.2 from 0.3.0
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 710)

import Control.Monad.Error

#else

import Control.Monad.Except

type ErrorT = ExceptT

runErrorT :: ErrorT e m a -> m (Either e a)
runErrorT = runExceptT

#endif
