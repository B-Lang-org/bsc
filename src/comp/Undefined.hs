{-# LANGUAGE DeriveDataTypeable #-}
module Undefined (
                  UndefKind(..),

                  uNotUsedInteger,
                  uDontCareInteger,
                  uNoMatchInteger,

                  integerToUndefKind,
                  undefKindToInteger
                 ) where

import Data.Data

import Eval

-- ============================================================

-- Undefined values in BSC carry information about their origin.
-- (The evaluator uses this for choosing error messages and optimizations.)

-- * UNotUsed is for values that we expect will never be used, such as
--   in unreachable code or the return value for an expression whose value
--   is unused.

-- * UNoMatch is the value returned from a case expression when no arm
--   matches but some value still needs to be returned.

-- * UDontCare is an explicit dont-care value written by the user, or
--   any other dont-care value that doesn't fit the above kinds.

data UndefKind = UNotUsed | UDontCare | UNoMatch
        deriving (Eq, Ord, Show, Data, Typeable)

instance Hyper UndefKind where
    hyper x y = seq x y

-- =====

uNotUsedInteger :: Integer
uNotUsedInteger  = 0

uDontCareInteger :: Integer
uDontCareInteger = 1

uNoMatchInteger :: Integer
uNoMatchInteger = 2

-- =====

integerToUndefKind :: Integer -> Maybe UndefKind
integerToUndefKind i
    | i == uNotUsedInteger  = Just UNotUsed
    | i == uDontCareInteger = Just UDontCare
    | i == uNoMatchInteger  = Just UNoMatch
    | otherwise             = Nothing

undefKindToInteger :: UndefKind -> Integer
undefKindToInteger UNotUsed  = uNotUsedInteger
undefKindToInteger UDontCare = uDontCareInteger
undefKindToInteger UNoMatch  = uNoMatchInteger

-- ============================================================
