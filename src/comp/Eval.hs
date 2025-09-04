module Eval (module Control.DeepSeq) where

import System.IO(Handle)
-- import Data.IntMap as IM
-- import Data.IntSet as IS
-- import Data.Set as DS
-- import Data.Map as DM
import FStringCompat(FString)
import Control.DeepSeq

instance NFData FString where
    rnf x = seq x ()

instance NFData Handle where
    -- TODO: Not sure this makes much sense, to be honest.
    rnf x = seq x ()

