{-# LANGUAGE CPP #-}
module SEMonad(SEM(..), err, run) where

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 710)
import Control.Applicative(Applicative(..))
#endif
import Control.Monad(liftM, ap)

newtype SEM e s a = M (s -> Either e (s, a))

instance Monad (SEM e s) where
    return a = M $ \ s -> Right (s, a)
    M a >>= f = M $ \ s ->
        case a s of
        Left e -> Left e
        Right (s', b) ->
            let M f' = f b
            in  f' s'

instance Functor (SEM e s) where
  fmap = liftM

instance Applicative (SEM e s) where
  pure = return
  (<*>) = ap

run :: s -> SEM e s a -> Either e (s, a)
run s (M m) = m s

err :: e -> SEM e s a
err msg = M (\s->Left msg)
