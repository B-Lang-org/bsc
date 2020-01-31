module IWireSet(
    IWireSet,
    wsEmpty,
    wsClock, wsReset,
    wsJoin, wsJoinMany,
    wsAddClock, wsAddReset, 
    wsGetClocks, wsGetResets,
    wsCheckClocks, wsCheckResets,
    wsGetClockDomain,
    wsIsEmpty,
    wsToProps
) where

-- Clock and reset tracking sets

import ListSet as LS
import Wires
import ISyntax
import Util(toMaybe)
import Data.Maybe(isJust)

-- clocks and resets that connected to a potentially dynamic objects
-- neither set is expected to get large normally
-- there are not expected to be a large (> 10) gating contributors
-- to a valid run-time expression
-- and more than one reset signal attached to a run-time expression
-- will trigger an "unsafe reset warning"
-- the only possible large case is when evaluating clock[s]Of or reset[s]Of
-- for a static object like a list (which should be unusual)
type IWireSet a = ([IClock a], [IReset a])

wsEmpty :: IWireSet a
wsEmpty = (LS.empty, LS.empty)

wsIsEmpty (cs,rs) = null cs && null rs

wsClock :: IClock a -> IWireSet a
wsClock c = (LS.singleton c, LS.empty)

-- resets do not contribute their synchronized clock
wsReset :: IReset a -> IWireSet a
wsReset r = (LS.empty, LS.singleton r)

wsJoin :: IWireSet a -> IWireSet a -> IWireSet a
wsJoin (a, b) (c, d) = (LS.union a c, LS.union b d)

wsJoinMany :: [IWireSet a] -> IWireSet a
wsJoinMany = foldr wsJoin wsEmpty

wsAddClock :: IClock a -> IWireSet a -> IWireSet a
wsAddClock c (cs, rs) = (LS.add c cs, rs)

-- resets do not contribute their synchronized clock
-- should they?
wsAddReset :: IReset a -> IWireSet a -> IWireSet a
wsAddReset r (cs, rs) = (cs, LS.add r rs)

wsGetClocks :: IWireSet a -> [IClock a]
wsGetClocks (cs,_) = LS.toList cs

wsGetResets :: IWireSet a -> [IReset a]
wsGetResets (_,rs) = filter (not . isNoReset) (LS.toList rs)

-- return a clock domain if there is a single valid one
wsGetClockDomain :: IWireSet a -> Maybe ClockDomain
wsGetClockDomain (cs, _) = case l' of 
                            [] -> Just noClockDomain
                            (c:cs) -> toMaybe (all (sameClockDomain c) cs) (getClockDomain c)
  where l  = LS.toList cs
        l' = filter (not . (inClockDomain noClockDomain)) l

wsCheckClocks :: IWireSet a -> Bool
wsCheckClocks ws = isJust (wsGetClockDomain ws)
        
wsCheckResets :: IWireSet a -> Bool
wsCheckResets (_, rs) = case l' of 
                         []   -> True
                         [_]  -> True -- a single meaningful reset
                         _    -> False -- more than one real reset
  where l  = LS.toList rs
        l' = filter (not . isNoReset) l 

wsToProps :: IWireSet a -> WireProps
wsToProps ws = WireProps { wpClockDomain = wsGetClockDomain ws,
                           wpResets = (map getResetId (wsGetResets ws)) }

