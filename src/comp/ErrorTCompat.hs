module ErrorTCompat (
       ErrorT,
       runErrorT,
       MonadError(..)
) where

import Control.Monad.Except

type ErrorT = ExceptT

runErrorT :: ErrorT e m a -> m (Either e a)
runErrorT = runExceptT
