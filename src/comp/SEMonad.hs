{-# LANGUAGE CPP #-}
module SEMonad where

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 710)
import Control.Applicative(Applicative(..))
#endif
import Control.Monad(liftM, ap)
#if !defined(__GLASGOW_HASKELL__) || ((__GLASGOW_HASKELL__ >= 800) && (__GLASGOW_HASKELL__ < 808))
import Control.Monad.Fail(MonadFail(..))
#endif
import ErrorUtil(internalError)

newtype SEM e s a = M (s -> Either e (s, a))

instance Monad (SEM e s) where
    return a = M $ \ s -> Right (s, a)
    M a >>= f = M $ \ s ->
        case a s of
	Left e -> Left e
	Right (s', b) ->
	    let M f' = f b
	    in  f' s'
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 808)
    fail msg = internalError ("SEMonad fail: " ++ msg)
#endif

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 800)
instance MonadFail (SEM e s) where
    fail msg = internalError ("SEMonad fail: " ++ msg)
#endif

instance Functor (SEM e s) where
  fmap = liftM

instance Applicative (SEM e s) where
  pure = return
  (<*>) = ap

run :: s -> SEM e s a -> Either e (s, a)
run s (M m) = m s

err :: e -> SEM e s a
err msg = M (\s->Left msg)

handle :: SEM e s a -> (e -> SEM e s a) -> SEM e s a
handle (M a) f = M $ \ s ->
    case a s of
    Left e -> let (M b) = f e in b s
    r -> r

-- if the state is composed of field constructors 
-- (or equivalent),
-- this function can extract a component of the
-- state.  E.g., see TIMonad
getComponent :: (s -> a) -> SEM e s a
getComponent f = M $ \s -> Right (s, f s)

modify :: (s -> s) -> SEM e s ()
modify f = M $ \s -> Right (f s, ())
