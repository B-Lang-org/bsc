module SimDomainInfo where

import Util(mapFst)

import ASyntax(AId, AExpr, AClock(..), ARuleId)
import Wires(ClockDomain)
import ErrorUtil(internalError)
import PPrint

import qualified Data.Map as M


-- ---------------

-- Id for indexing into the domain map.
-- The APackage lists domains by number.  Rather than reassigning new
-- unique numbers, we'll store a domain by the instance name and the number
-- in that instance.  If a domain of an instance is the same as its parent,
-- then we use the parent Id as the index and forget the child Id.
type DomainId = (AId, ClockDomain)

-- ---------------

-- Mapping from a clock to its domain id
-- (because we might optimize known const gates to 1,
--  we map only from the oscillator field of the clock)
type DomainIdMap = M.Map AExpr DomainId

makeDomainIdMap :: [(AClock, DomainId)] -> DomainIdMap
makeDomainIdMap = M.fromList . mapFst aclock_osc

findMaybeDomainId :: DomainIdMap -> AClock -> Maybe DomainId
findMaybeDomainId id_map aclk = M.lookup (aclock_osc aclk) id_map

findDomainId :: DomainIdMap -> AClock -> DomainId
findDomainId id_map aclk =
    case (findMaybeDomainId id_map aclk) of
        Just i -> i
        Nothing -> internalError ("SimDomainInfo.findDomainId: cannot find " ++
                                  ppReadable aclk ++
                                  ppReadable (M.toList id_map))

-- ---------------

data DomainInfo = DomainInfo
    {
      -- clocks which are in this domain
      di_clocks :: [AClock],
      -- domain identifiers
      -- (starts with just the child domain Id and gets any parent Ids)
      di_domains :: [DomainId],
      -- rules in the clock domain
      di_rules :: [ARuleId],
      -- rules in the clock domain with the (* clock_crossing_rule *) pragma
      di_clock_crossing_rules :: [ARuleId],
      -- primitive submods which need to be clocked by this clock
      --   pairs the primitive instance Id (hierarchical)
      --   with the name of the clock arg that the clock is connected to,
      --   and the clock that is connected.
      di_prims :: [(AId, (AId, AClock))],
      -- primitive submods with resets synchronized on this clock
      -- (paired with the Id of the clock argument to the module)
      di_prim_resets :: [(AId, AId)],
      -- output clocks, pairing the output name with the value
      di_output_clocks :: [(AId, AClock)],
      -- clock susbtitutions
      -- (for replacing gate references in the rule conditions)
      di_clock_substs :: ClockSubst
    }
  deriving (Eq, Show)

instance PPrint DomainInfo where
    pPrint d _ di =
        (text "DomainInfo") $+$
        text "clocks: " <+> pPrint d 0 (di_clocks di) $+$
        text "domains: " <+> pPrint d 0 (di_domains di) $+$
--        text "rules:"   <+> pPrint d 0 (di_rules di) $+$
        text "-- Primitives" $+$
        vsep (map (pPrint d 0) (di_prims di)) $+$
        text "-- Primitives with resets in this domain" $+$
        vsep (map (pPrint d 0) (di_prim_resets di)) $+$
        text "-- Output clocks" $+$
        vsep (map (pPrint d 0) (di_output_clocks di)) $+$
        text "-- Clocks substitutions" $+$
        vsep (map (pPrint d 0) (di_clock_substs di))

-- ---------------

-- Mapping from a clock to the rules in its domain
type DomainInfoMap = M.Map DomainId DomainInfo

findDomainInfo :: DomainInfoMap -> DomainId -> DomainInfo
findDomainInfo dinfo_map dom_id =
    case (M.lookup dom_id dinfo_map) of
        Just i -> i
        Nothing -> internalError
                       ("SimDomainInfo.findDomainInfo: cannot find " ++
                        ppReadable dom_id ++
                        ppReadable (M.toList dinfo_map))

-- ---------------

type ClockSubst = [(AClock, AClock)]

applyClockSubst :: ClockSubst -> AClock -> AClock
applyClockSubst ss a =
    case (lookup a ss) of
        Nothing -> a
        Just a' -> a'

-- ---------------

