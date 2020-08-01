{-# LANGUAGE CPP #-}
module ErrorTCompat (
       ErrorT,
       runErrorT,
       MonadError(..),
       lift
) where

import Control.Monad.Except

type ErrorT = ExceptT

runErrorT :: ErrorT e m a -> m (Either e a)
runErrorT = runExceptT
