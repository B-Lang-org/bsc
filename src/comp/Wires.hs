{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
module Wires(ClockId, ClockDomain(..), ResetId,
             nextClockId, nextClockDomain, nextResetId,
             initClockId, initClockDomain, initResetId,
             noClockId, noClockDomain, noResetId,
             noDefaultClockId, noDefaultResetId,
             WireProps(..), emptyWireProps,
             writeClockDomain, readClockDomain,
             writeResetId, readResetId
             ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Eval
import PPrint
import qualified Data.Generics as Generic
import GHC.Generics (Generic)
-- Primitives for describing special wires (e.g. clock and reset)

data ClockId = ClockId !Int
  deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable, Generic, NFData)

data ClockDomain = ClockDomain !Int
  deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable, Generic, NFData)

instance PPrint ClockDomain where
  pPrint d p (ClockDomain i) = pPrint d p i

data ResetId = ResetId !Int
  deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable, Generic, NFData)

instance PPrint ResetId where
  pPrint d p (ResetId i) = pPrint d p i

{-# INLINE nextClockId #-}
nextClockId :: ClockId -> ClockId
nextClockId (ClockId i) = (ClockId (i + 1))

{-# INLINE nextResetId #-}
nextResetId :: ResetId -> ResetId
nextResetId (ResetId i) = (ResetId (i + 1))

{-# INLINE nextClockDomain #-}
nextClockDomain :: ClockDomain -> ClockDomain
nextClockDomain (ClockDomain d) = (ClockDomain (d + 1))

{-# INLINE initClockId #-}
initClockId :: ClockId
initClockId = (ClockId 0)

{-# INLINE initResetId #-}
initResetId :: ResetId
initResetId = (ResetId 0)

{-# INLINE initClockDomain #-}
initClockDomain :: ClockDomain
initClockDomain = (ClockDomain 0)

noClockId :: ClockId
noClockId = (ClockId (-1))

noDefaultClockId :: ClockId
noDefaultClockId = ClockId (-2)

noClockDomain :: ClockDomain
noClockDomain = (ClockDomain (-1))

noResetId :: ResetId
noResetId = (ResetId (-1))

noDefaultResetId :: ResetId
noDefaultResetId = ResetId (-2)

data WireProps = WireProps { -- clock domain of object, Nothing if object crosses clock domains
                             wpClockDomain :: Maybe ClockDomain,
                             -- identifiers of reset signals connected to object
                             -- more than one implies "unsafe reset crossing"
                             wpResets :: [ResetId]
                           }
   deriving(Eq, Ord, Show, Generic.Data, Generic.Typeable, Generic, NFData)

emptyWireProps :: WireProps
emptyWireProps = WireProps { wpClockDomain = Nothing, wpResets = [] }

instance PPrint WireProps where
  pPrint d p wp = text ("clock domain = ") <> (pPrint d 0 (wpClockDomain wp)) <> text (",") <+>
                  text ("resets = ") <> (pPrint d 0 (wpResets wp))

-----

-- Functions for writing and reading ClockDomain to a file

writeClockDomain :: ClockDomain -> Int
writeClockDomain (ClockDomain i) = i

readClockDomain :: Int -> ClockDomain
readClockDomain i = ClockDomain i

-----

-- Functions for writing and reading ResetId to a file

writeResetId :: ResetId -> Int
writeResetId (ResetId i) = i

readResetId :: Int -> ResetId
readResetId i = ResetId i

-----
