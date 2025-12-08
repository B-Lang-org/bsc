{-# LANGUAGE DeriveDataTypeable #-}
module Backend (
                Backend(..),
                backendMatches
                ) where

import qualified Data.Generics as Generic
import PPrint
import Eval

-- ===============

data Backend = Bluesim | Verilog
             deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

instance PPrint Backend where
    pPrint _ _ Bluesim = text "Bluesim"
    pPrint _ _ Verilog = text "Verilog"

instance NFData Backend where
    rnf Bluesim = ()
    rnf Verilog = ()

-- ===============

-- Does the backend of an ABin match the backend expected
backendMatches :: Maybe Backend -> Maybe Backend -> Bool
backendMatches _ Nothing = True
backendMatches Nothing _ = True
backendMatches (Just expected) (Just actual) = (expected == actual)

-- ===============

