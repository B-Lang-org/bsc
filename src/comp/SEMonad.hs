{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module SEMonad(SEM(..), run) where

import Control.Monad.Except
import Control.Monad.State

newtype SEM e s a =  M { unSEM :: ExceptT e (State s) a }
    deriving (Applicative, Functor, Monad, MonadError e, MonadState s)

run :: SEM e s a -> s -> Either e (a, s)
run m s = case runState (runExceptT (unSEM m)) s of
                    (Left e, _) -> Left e
                    (Right r, s) -> Right (r, s)
