{-# LANGUAGE DeriveDataTypeable #-}
module SpeedyString(SString, toString, fromString, (++), concat, filter) where

import Prelude hiding((++), concat, filter)
import qualified Prelude((++), filter)
import Hash(Hashable(..))
import IOMutVar(MutableVar, newVar, readVar, writeVar)
import System.IO.Unsafe(unsafePerformIO)
import qualified Data.IntMap as M
-- import qualified NotSoSpeedyString
import ErrorUtil (internalError)
import qualified Data.Generics as Generic


data SString = SString !Int -- unique id
   deriving (Generic.Data, Generic.Typeable)

instance Eq SString where
    (SString i) == (SString i') = i == i'

-- note that Ord is not the usual string ordering
instance Ord SString where
    compare (SString i) (SString i') = compare i i'

instance Show SString where
    show = show . toString

instance Hashable SString where
    hash (SString i) = hash i

-- public

toString :: SString -> String
toString (SString id) = unsafePerformIO $
			do m <- readVar strings
			   return $ M.findWithDefault err id m

fromString :: String -> SString
fromString s = unsafePerformIO $
	       do m <- readVar sstrings
		  return $ maybe (newSString s) id $ M.lookup (hashStr s) m >>= lookup s

(++) :: SString -> SString -> SString
s ++ s' = fromString $ (toString s) Prelude.++ (toString s')

concat :: [SString] -> SString
concat = fromString . concatMap toString

filter :: (Char -> Bool) -> SString -> SString
filter pred s = fromString $ Prelude.filter pred (toString s)

-- private

newSString :: String -> SString
newSString s = unsafePerformIO $
	       do id <- freshInt
		  let ss = SString id
		  sm <- readVar strings
		  ssm <- readVar sstrings
		  writeVar strings $ M.insert id s sm
		  writeVar sstrings $ M.insertWith (Prelude.++)
                                          (hashStr s) [(s,ss)] ssm
		  return ss

err = internalError "SpeedyString: inconsistent representation"

--toNotSoSpeedyString :: SString -> NotSoSpeedyString.SString
--toNotSoSpeedyString speedy = NotSoSpeedyString.fromString (toString speedy)

--fromNotSoSpeedyString :: NotSoSpeedyString.SString -> SString
--fromNotSoSpeedyString not_so_speedy =
--    fromString (NotSoSpeedyString.toString not_so_speedy)

-- internal representation

strings :: MutableVar (M.IntMap String)
strings = unsafePerformIO $ newVar (M.empty)

sstrings :: MutableVar (M.IntMap [(String, SString)])
sstrings = unsafePerformIO $ newVar (M.empty)


-- string hash function, stolen from FString

hashStr :: String -> Int
hashStr s = f s 0
        where f "" r = r
              f (c:cs) r = f cs (r*16+r+fromEnum c)


-- unique id factory

nextInt :: MutableVar Int
nextInt = unsafePerformIO $ (newVar 0)

freshInt :: IO Int
freshInt = do fresh <- readVar nextInt
	      writeVar nextInt (fresh + 1)
	      return fresh
