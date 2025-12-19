{-# LANGUAGE CPP #-}
module AScheduleInfo (
    AScheduleErrInfo(..),
    AScheduleInfo(..),
    Conflicts(..),
    ExclusiveRulesDB(..),
    FastSchedNode(..),
    RuleRelationDB(..),
    RuleRelationInfo(..),
    SchedNode(..),
    areRulesDisjoint,
    areRulesExclusive,
    defaultRuleRelationship,
    erdbFromList,
    erdbToList,
    getRuleRelation,
    getSchedNodeId,
    isSchedNode,
    printRuleRelationInfo,
    rrdbFromList,
    unionRuleRelationInfo
) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List(intersperse)
import Util(thd)
import Eval

import ErrorUtil
import PFPrint
import Position
import Id(cmpIdByName)
import ASyntax
import AUses
import VModInfo(VSchedInfo)
import RSchedule(RAT)


-- ========================================================================
-- Data returned by the aSchedule stage
--

data AScheduleInfo = AScheduleInfo
    {
      -- Warnings during scheduling
      -- (position, tag, msg including position and tag)
      --
      asi_warnings             :: [(Position, String, String)],

      -- In order of computation in ASchedule:

      -- The method uses map and the rule uses map
      --   They don't have any read method calls used by a rule's assumptions.
      --   XXX except where necessary to make AState work
      --   The rule uses map also doesn't have the method calls to write a
      --   rule's conflict-free condition wires (the method uses map does
      --   because AState needs it).
      --   This will probably change somehow when we have real runtime errors
      --
      asi_method_uses_map      :: MethodUsesMap,
      asi_rule_uses_map        :: RuleUsesMap,

      asi_resource_alloc_table :: RAT,
      asi_exclusive_rules_db   :: ExclusiveRulesDB,
      asi_sched_order          :: [SchedNode],
      asi_schedule             :: ASchedule,
      asi_sched_graph          :: [(SchedNode, [SchedNode])],
      asi_rule_relation_db     :: RuleRelationDB,
      asi_v_sched_info         :: VSchedInfo
    } deriving (Show)


instance PPrint AScheduleInfo where
    pPrint d p asi =
        text "AScheduleInfo" $+$
        nest 2 (
            text "-- schedule" $+$
            pPrint d 0 (asi_schedule asi) $+$
            text "-- vschedinfo" $+$
            pPrint d 0 (asi_v_sched_info asi) $+$
            text "-- warnings" $+$
            (let ppWarn = vcat . map text . lines
             in  vcat (map (ppWarn . thd) (asi_warnings asi))) $+$
            text "-- method uses map" $+$
            pPrint d 0 (asi_method_uses_map asi) $+$
            text "-- rule uses map" $+$
            pPrint d 0 (asi_rule_uses_map asi) $+$
            text "-- resource allocation table" $+$
            pPrint d 0 (asi_resource_alloc_table asi)
            -- no dump of DBs, sched graph and order
            )


-- ---------------

-- When the scheduling stage aborts with an error, this data structure
-- contains the available information up to that point (for debugging)
--
data AScheduleErrInfo = AScheduleErrInfo
    {
      -- Warnings during scheduling
      -- (position, tag, msg including position and tag)
      --
      asei_warnings             :: [(Position, String, String)],

      -- Errors during scheduling
      -- (position, tag, msg including position and tag)
      --
      asei_errors               :: [(Position, String, String)],

      -- These are computed initially, and therefore are always available:

      -- The method uses map and the rule uses map
      --   They don't have any read method calls used by a rule's assumptions.
      --   XXX except where necessary to make AState work
      --   The rule uses map also doesn't have the method calls to write a
      --   rule's conflict-free condition wires (the method uses map does
      --   because AState needs it).
      --   This will probably change somehow when we have real runtime errors
      --
      asei_method_uses_map      :: MethodUsesMap,
      asei_rule_uses_map        :: RuleUsesMap,

      -- The remaining fields may not be available.
      -- In order of computation:
      --
      asei_resource_alloc_table :: Maybe RAT,
      asei_exclusive_rules_db   :: Maybe ExclusiveRulesDB,
      asei_sched_order          :: Maybe [SchedNode],
      asei_schedule             :: Maybe ASchedule,
      asei_sched_graph          :: Maybe [(SchedNode, [SchedNode])],
      asei_rule_relation_db     :: Maybe RuleRelationDB,
      asei_v_sched_info         :: Maybe VSchedInfo
    } deriving (Show)


instance PPrint AScheduleErrInfo where
    pPrint d p asei =
        text "AScheduleErrInfo" $+$
        nest 2 (
            text "-- schedule" $+$
            pPrint d 0 (asei_schedule asei) $+$
            text "-- vschedinfo" $+$
            pPrint d 0 (asei_v_sched_info asei) $+$
            text "-- warnings" $+$
            (let ppWarn = vcat . map text . lines
             in  vcat (map (ppWarn . thd) (asei_warnings asei))) $+$
            text "-- errors" $+$
            (let ppErr = vcat . map text . lines
             in  vcat (map (ppErr . thd) (asei_errors asei))) $+$
            text "-- method uses map" $+$
            pPrint d 0 (asei_method_uses_map asei) $+$
            text "-- rule uses map" $+$
            pPrint d 0 (asei_rule_uses_map asei) $+$
            text "-- resource allocation table" $+$
            pPrint d 0 (asei_resource_alloc_table asei)
            -- no dump of DBs, sched graph and order
            )


-- ---------------

-- A cache of what is known about whether rules are exclusive (post-scheduling)
-- It can be queried for two pieces of information:
-- * Are the CAN_FIRE signals for the rules disjoint?
-- * Are the WILL_FIRE signals for the rules disjoint?
--   (This is a superset which also takes into account rule executions
--    that have been forced to be exclusive due to conflicts etc.)
newtype ExclusiveRulesDB =
    ExclusiveRulesDB (M.Map ARuleId (S.Set ARuleId, S.Set ARuleId))

-- Are the WILL_FIRE signals of the rules exclusive?
-- (Used in Verilog backend for determining if a priority mux is needed.)
-- Note: we check both the disjoint set and the exclusive set, since we
-- do not make a redundant record of exclusivity when it is implied by
-- disjointness.
areRulesExclusive :: ExclusiveRulesDB -> ARuleId -> ARuleId -> Bool
areRulesExclusive (ExclusiveRulesDB exclusive_fmap) r1 r2 =
    let (disj_set, excl_set) = M.findWithDefault (S.empty, S.empty) r1 exclusive_fmap
    in (S.member r2 disj_set) || (S.member r2 excl_set)

-- Are the CAN_FIRE signals of the rules exclusive?
-- (Used in Bluesim backend for short-circuiting the CF computation,
-- particularly to avoid computing a CF which has changed due to the
-- execution of a mutually exclusive rule -- for which no sched edge exists.)
areRulesDisjoint :: ExclusiveRulesDB -> ARuleId -> ARuleId -> Bool
areRulesDisjoint (ExclusiveRulesDB exclusive_fmap) r1 r2 =
    let (disj_set, _) = M.findWithDefault (S.empty, S.empty) r1 exclusive_fmap
    in  S.member r2 disj_set

erdbToList :: ExclusiveRulesDB -> [(ARuleId,([ARuleId],[ARuleId]))]
erdbToList (ExclusiveRulesDB exclusive_map) =
    let conv (r, (d_set, e_set)) = (r, (S.toList d_set, S.toList e_set))
    in  map conv (M.toList exclusive_map)

erdbFromList :: [(ARuleId,([ARuleId],[ARuleId]))] -> ExclusiveRulesDB
erdbFromList xs =
    let conv (r, (ds, es)) = (r, (S.fromList ds, S.fromList es))
    in  ExclusiveRulesDB (M.fromList (map conv xs))

instance Show ExclusiveRulesDB where
    show erdb = show (erdbToList erdb)

-- ---------------

data SchedNode = Sched AId | Exec AId
  deriving (Eq, Show)

-- comparing by name instead of the default ORD instance for Id
-- makes the schedule order from the flattened graph stable.
instance Ord SchedNode where
  compare (Sched _) (Exec _)  = LT
  compare (Exec _)  (Sched _) = GT
  compare (Sched x) (Sched y) = cmpIdByName x y
  compare (Exec x)  (Exec y)  = cmpIdByName x y

instance PPrint SchedNode where
    pPrint d _ (Sched i) = text "Sched" <+> pPrint d 0 i
    pPrint d _ (Exec i) = text "Exec" <+> pPrint d 0 i

getSchedNodeId :: SchedNode -> AId
getSchedNodeId (Sched i) = i
getSchedNodeId (Exec i) = i

isSchedNode :: SchedNode -> Bool
isSchedNode (Sched _) = True
isSchedNode (Exec _) = False

-- A SchedNode newtype wrapper for SchedNode for the cases
-- where comparison performance is critical and stable ordering
-- is not important.
newtype FastSchedNode = FSN { unFSN :: SchedNode }
  deriving(Eq)

instance Ord FastSchedNode where
  compare (FSN (Sched _)) (FSN (Exec _))  = LT
  compare (FSN (Exec _))  (FSN (Sched _)) = GT
  compare (FSN (Sched x)) (FSN (Sched y)) = compare x y
  compare (FSN (Exec x))  (FSN (Exec y))  = compare x y


-- ---------------

-- This structure represents information about pairs of rules:
--   - If a pair is not in the set, then their predicates are not disjoint
--   - If a pair is not in the map, then the rules have no conflicts
--   - If a pair maps to a RuleRelationInfo value, then the breakdown
--     of conflicts is given in the RuleRelationInfo structure.
data RuleRelationDB =
    RuleRelationDB (S.Set (ARuleId,ARuleId))                  -- disjointness
                   (M.Map (ARuleId,ARuleId) RuleRelationInfo) -- conflicts

data RuleRelationInfo = RuleRelationInfo { mCF :: Maybe Conflicts
                                         , mSC :: Maybe Conflicts
                                         , mRes :: Maybe Conflicts
                                         , mCycle :: Maybe Conflicts
                                         , mPragma :: Maybe Conflicts
                                         , mArb :: Maybe Conflicts
                                         -- XXX path and urgency info?
                                         } deriving (Eq,Show)

defaultRuleRelationship :: RuleRelationInfo
defaultRuleRelationship = RuleRelationInfo { mCF     = Nothing
                                           , mSC     = Nothing
                                           , mRes    = Nothing
                                           , mCycle  = Nothing
                                           , mPragma = Nothing
                                           , mArb    = Nothing
                                           }


rrdbToList :: RuleRelationDB ->
              [((ARuleId,ARuleId),Bool,(Maybe RuleRelationInfo))]
rrdbToList (RuleRelationDB dset cmap) =
    let all_pairs = dset `S.union` (M.keysSet cmap)
    in [ (k, k `S.member` dset, M.lookup k cmap) | k <- S.toList all_pairs ]

rrdbFromList :: [((ARuleId,ARuleId),Bool,(Maybe RuleRelationInfo))] ->
                RuleRelationDB
rrdbFromList xs =
    let dset = S.fromList [ k | (k,True,_) <- xs ]
        cmap = M.fromList [ (k,rri) | (k,_,(Just rri)) <- xs ]
    in RuleRelationDB dset cmap

instance Show RuleRelationDB where
    show rrdb = show (rrdbToList rrdb)

getRuleRelation :: RuleRelationDB -> ARuleId -> ARuleId -> (Bool,RuleRelationInfo)
getRuleRelation (RuleRelationDB dset cmap) r1 r2 =
    let disj = S.member (r1,r2) dset
        rri  = M.findWithDefault defaultRuleRelationship (r1,r2) cmap
    in (disj,rri)

-- -----

data Conflicts =
      CUse [(MethodId,MethodId)]
    | CCycle [ARuleId]
    | CMethodsBeforeRules
    | CUserEarliness Position
    | CUserAttribute Position
    | CUserPreempt Position
    | CResource MethodId
    | CArbitraryChoice
    | CFFuncArbitraryChoice
  deriving (Eq,Show)

printConflicts :: Bool -> PDetail -> Conflicts -> Doc
printConflicts use_pvprint d edge =
    let pfp :: (PVPrint a, PPrint a) => a -> Doc
        pfp = if (use_pvprint)
              then pvPrint d 0
              else pPrint d 0
    in  case (edge) of
            (CUse uses) ->
                let meths = vcat [pfp m1 <+> text "vs." <+> pfp m2
                                     | (m1, m2) <- uses]
                in  fsep [s2par "calls to", nest 2 meths]
            (CCycle cycle_rules) ->
                let cycle = fsep (intersperse (text "->")
                                    [pfp r | r <- cycle_rules])
                in  fsep [s2par "dropped cycle", nest 2 $ parens cycle]
            (CMethodsBeforeRules) ->
                s2par "methods fire before rules"
            (CUserEarliness pos) ->
                fsep [s2par "earliness attribute at", pfp pos]
            (CUserAttribute pos) ->
                fsep [s2par "scheduling attribute at", pfp pos]
            (CUserPreempt pos) ->
                fsep [s2par "preempt attribute at", pfp pos]
            (CResource m) -> fsep [s2par "resource limit on", pfp m]
            (CArbitraryChoice) ->
                s2par "earliness order chosen by the compiler"
            (CFFuncArbitraryChoice) ->
                s2par ("earliness order chosen by the compiler" ++
                       " (due to system task or foreign function use)")

instance PPrint Conflicts where
    pPrint d p = printConflicts False d

instance PVPrint Conflicts where
    pvPrint d p = printConflicts True d

instance NFData Conflicts where
    rnf (CUse uses) = rnf uses
    rnf (CCycle cycle_rules) = rnf cycle_rules
    rnf (CMethodsBeforeRules) = ()
    rnf (CUserEarliness pos) = rnf pos
    rnf (CUserAttribute pos) = rnf pos
    rnf (CUserPreempt pos) = rnf pos
    rnf (CResource m) = rnf m
    rnf (CArbitraryChoice) = ()
    rnf (CFFuncArbitraryChoice) = ()

instance NFData AScheduleInfo where
  rnf (AScheduleInfo w m r rat er so sched graph rrdb vsi) =
    rnf10 w m r rat er so sched graph rrdb vsi

instance NFData ExclusiveRulesDB where
  rnf (ExclusiveRulesDB m) = rnf m

instance NFData SchedNode where
  rnf (Sched aid) = rnf aid
  rnf (Exec aid) = rnf aid

instance NFData RuleRelationDB where
  rnf (RuleRelationDB s m) = rnf2 s m

instance NFData RuleRelationInfo where
  rnf (RuleRelationInfo cf sc res cyc ps arb) = rnf6 cf sc res cyc ps arb

-- -----

printRuleRelationInfo :: ARuleId -> ARuleId -> Bool -> RuleRelationInfo -> Doc
printRuleRelationInfo rule1 rule2 isDisjoint
        (RuleRelationInfo mCF mSC mRes mCycle mPragma mArb) =
    let
        -- print a single conflict of a given type
        pp_conflict ctype Nothing =
            sep [text "no", text ctype, text "conflict"]
        pp_conflict ctype (Just c) =
            sep [text ctype, text "conflict:", pPrint PDReadable 0 c]
    in
        (text "Scheduling info for rules \"" <>
         pPrint PDReadable 0 rule1 <> text "\" and \"" <>
         pPrint PDReadable 0 rule2 <> text "\":")
        $+$
        sep [text "predicates",
             (if isDisjoint
              then text "are" else text "are not"),
              text "disjoint"]
        $+$
        nest 4 (pp_conflict "<>" mCF $+$
                pp_conflict "<" mSC $+$
                pp_conflict "resource" mRes $+$
                pp_conflict "cycle" mCycle $+$
                pp_conflict "attribute" mPragma)
                -- XXX mArb

-- -----

unionRuleRelationInfo :: RuleRelationInfo -> RuleRelationInfo ->
                         RuleRelationInfo
unionRuleRelationInfo rri1 rri2 =
    let
        unionMaybeWith fn Nothing   m2        = m2
        unionMaybeWith fn m1        Nothing   = m1
        unionMaybeWith fn (Just v1) (Just v2) = Just (fn v1 v2)

        unionCUse (CUse us1) (CUse us2) = CUse (us1 ++ us2)
        unionCUse c1 c2 = internalError ("unionCUse: " ++ ppReadable (c1, c2))

        -- XXX the info in c2 is lost
        unionCResource c1@(CResource _) (CResource _) = c1
        unionCResource c1 c2 = internalError ("unionCResource: " ++
                                              ppReadable (c1, c2))

        -- XXX the info in c2 is lost
        unionCCycle c1@(CCycle _) (CCycle _) = c1
        unionCCycle c1 c2 = internalError ("unionCCycle: " ++
                                           ppReadable (c1, c2))

        -- XXX the info in c2 is lost
        unionPragma c1 c2 = c1

        -- XXX Since some info may be lost, make sure that any reason
        -- XXX othet than FFunc bias trumps FFunc bias
        unionArb CArbitraryChoice _ = CArbitraryChoice
        unionArb _ CArbitraryChoice = CArbitraryChoice
        unionArb c1 c2 = c1

    in
       RuleRelationInfo {
           mCF = unionMaybeWith unionCUse (mCF rri1) (mCF rri2),
           mSC = unionMaybeWith unionCUse (mSC rri1) (mSC rri2),
           mRes = unionMaybeWith unionCResource (mRes rri1) (mRes rri2),
           mCycle = unionMaybeWith unionCCycle (mCycle rri1) (mCycle rri2),
           mPragma = unionMaybeWith unionPragma (mPragma rri1) (mPragma rri2),
           mArb = unionMaybeWith unionArb (mArb rri1) (mArb rri2)
       }

-- ---------------
