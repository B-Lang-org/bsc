{-# LANGUAGE DeriveDataTypeable #-}
module Backend (
                Backend(..),
                backendMatches
                ) where

import Data.Data
import Data.Typeable

import PPrint
import Eval

-- ===============

data Backend = Bluesim | Verilog
             deriving (Eq, Ord, Show, Data, Typeable)

instance PPrint Backend where
    pPrint _ _ Bluesim = text "Bluesim"
    pPrint _ _ Verilog = text "Verilog"

instance Hyper Backend where
    hyper x y = (x==x) `seq` y

-- ===============

-- Does the backend of an ABin match the backend expected
backendMatches :: Maybe Backend -> Maybe Backend -> Bool
backendMatches _ Nothing = True
backendMatches Nothing _ = True
backendMatches (Just expected) (Just actual) = (expected == actual)

-- ===============
