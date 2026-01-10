{-# LANGUAGE CPP #-}
module ASchedule(
                 aSchedule,
                 extractCFPairsSP,
                 extractMEPairsSP,
                 errAction,
                 AScheduleInfo(..), AScheduleErrInfo(..),

                 -- elements of AScheduleInfo
                 MethodUsesMap, MethodUsers, MethodId(..), UniqueUse(..),
                 RAT,
                 ExclusiveRulesDB(..),
                 areRulesExclusive
                 ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List
import Data.Maybe
import Control.Monad(when, foldM)
import Control.Monad.Except(ExceptT, runExceptT, throwError)
import Control.Monad.State(StateT, runStateT, lift, get, put)
import System.IO.Unsafe
import Debug.Trace(traceM)
import qualified Data.Map as M
import qualified Data.Set as S

import qualified GraphMap as G
import qualified GraphWrapper as GW
import qualified GraphUtil as GU
import GraphPaths
import ASyntax
import ASyntaxUtil
import Backend
import Pragma
import Util
import Eval
import Version(bscVersionStr)
import Error(internalError, EMsg, WMsg, EMsgs(..), ErrMsg(..),
             ErrorHandle, bsError, bsErrorNoExit, bsWarning,
             showErrorList, showWarningList, getErrMsgTag)
import ErrorMonad(ErrorMonad(..))
import PFPrint
import PPrint(vsep, commaSep)
import SCC(scc,tsort)
import Id(Id, emptyId, getIdString, getIdBaseString, getIdPosition,
          isRdyId, addToBase, mk_homeless_id, mkIdWillFire, addSuffix)
import Position
import Flags(Flags(..))
import VModInfo(vSched, vFields, VSchedInfo, VMethodConflictInfo, VFieldInfo(..))
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import IOUtil(progArgs)
import FileNameUtil
import FileIOUtil(writeFileCatch)
import TopUtils(putStrLnF, mkTimestampComment)
import AUses(-- re-exported interface
             MethodUsesMap, MethodUsers, MethodId(..), UniqueUse(..),
             MethodUsesList,
             -- internally used interface
             RuleId,
             {- methodIdToId, -} extractCondition,
             buildUseMaps, getMIdPosition, getUUPos,
             Rule(..), ruleName, rulePred, ruleAncestor,
             RuleUsesMap,
             rumToObjectMap, rumToMethodUseMap,
             rumGetMethodIds, rumRuleUsesFF,
             getMethodActionUses, rumGetActionUses, lookupMethodActionUse)
import Wires(WireProps(..), ClockDomain(..))
import APaths(PathUrgencyPairs, PathNode)
import AScheduleInfo
import RSchedule(rSchedule, RAT)
import DisjointTest(DisjointTestState, initDisjointTestState,
                    checkDisjointExprWithCtx,
                    RuleDisjointTest, genDisjointSet)
import DOT
import PreIds(idErrorTask)

-- ========================================================================
-- Traces
--

trace_ncsets :: Bool
trace_ncsets = "-trace-ncsets" `elem` progArgs
trace_usemap :: Bool
trace_usemap = "-trace-usemap" `elem` progArgs
trace_mutatormap :: Bool
trace_mutatormap = "-trace-mutatormap" `elem` progArgs
trace_cfmap :: Bool
trace_cfmap = "-trace-cfmap" `elem` progArgs
trace_cfmaps :: Bool
trace_cfmaps = "-trace-cfmaps" `elem` progArgs
trace_pcmap :: Bool
trace_pcmap = "-trace-pcmap" `elem` progArgs
trace_pcmaps :: Bool
trace_pcmaps = "-trace-pcmaps" `elem` progArgs
trace_scmap :: Bool
trace_scmap = "-trace-scmap" `elem` progArgs
trace_scmaps :: Bool
trace_scmaps = "-trace-scmaps" `elem` progArgs
trace_scgraph :: Bool
trace_scgraph = "-trace-scgraph" `elem` progArgs
trace_seqgraph :: Bool
trace_seqgraph = "-trace-seqgraph" `elem` progArgs
trace_schedinfo :: Bool
trace_schedinfo = "-trace-schedinfo" `elem` progArgs
trace_sched_steps :: Bool
trace_sched_steps = "-trace-sched-steps" `elem` progArgs
trace_disjoint_tests :: Bool
trace_disjoint_tests = "-trace-disjoint-tests" `elem` progArgs
trace_defs :: Bool
trace_defs           = "-trace-a-definitions" `elem` progArgs
trace_no_urgency_edge :: Bool
trace_no_urgency_edge = "-trace-no-urgency-edge" `elem` progArgs
disable_urgency_warnings :: Bool
disable_urgency_warnings = "-hack-disable-urgency-warnings" `elem` progArgs

pp :: Doc -> String
pp = pretty 78 78


-- ========================================================================
-- Conflict set and graph data structures
--

-- SET of non-conflicting methods
newtype NoConflictSet = NoConflictSet (S.Set (MethodId, MethodId))

instance PPrint NoConflictSet where
    pPrint d p (NoConflictSet s) = pPrint d p (S.toList s)

-- --------------------

type ConflictMap = G.GraphMap ARuleId [Conflicts]

addConflictEdge :: ConflictMap -> (ARuleId, ARuleId, [Conflicts]) -> ConflictMap
addConflictEdge g e = G.addEdgeWith (++) g e

-- From a list of conlifct explanations, pick one to report.
-- For backwards compatibility, we choose the most recently added;
-- but we could choose to always return a method-use explanation if one
-- exists, or to return a user-attribute explanation, etc.
getConflict :: [Conflicts] -> Conflicts
getConflict (c:_) = c
getConflict [] = internalError ("getConflict: empty list")

lookupUseConflict :: (ARuleId, ARuleId) -> ConflictMap -> Maybe Conflicts
lookupUseConflict k cmap = G.lookup k cmap >>= getUseConflict

getConflictWith :: (Conflicts -> Bool) -> [Conflicts] -> Maybe Conflicts
getConflictWith fn (c : cs) | fn c = Just c
                            | otherwise = getConflictWith fn cs
getConflictWith fn [] = Nothing

getUseConflict :: [Conflicts] -> Maybe Conflicts
getUseConflict cs =
    let isUseConflict (CUse {}) = True
        isUseConflict _         = False
    in  getConflictWith isUseConflict cs

getCycleConflict :: [Conflicts] -> Maybe Conflicts
getCycleConflict cs =
    let isCycleConflict (CCycle {}) = True
        isCycleConflict _         = False
    in  getConflictWith isCycleConflict cs


-- ========================================================================
-- Urgency graph data structures

data UrgencyEdge = UEUser [Position]
                 | UEMethodUse [PathNode]
                 | UEArbitraryChoice
                 deriving (Show, Eq)

type UrgencyMap = G.GraphMap ARuleId UrgencyEdge

printUrgencyEdge :: Bool -> PDetail -> Int -> UrgencyEdge -> Doc
printUrgencyEdge use_pvprint d p edge =
    let pp :: (PVPrint a, PPrint a) => a -> Doc
        pp = if (use_pvprint)
             then pvPrint d p
             else pPrint d p
    in  case (edge) of
            (UEUser poss) ->
                s2par "user urgencies located at the following positions:" $$
                nest 2 (vcat (map (pp) poss))
            (UEMethodUse path) ->
                s2par "the following data dependency:" $$
                nest 2 (pp path)
            (UEArbitraryChoice) ->
                s2par "urgency order chosen by the compiler"

instance PPrint UrgencyEdge where
    pPrint d p = printUrgencyEdge False d p

instance PVPrint UrgencyEdge where
    pvPrint d p = printUrgencyEdge True d p


-- This is the actual print used in error messages
printUrgencyEdgePair :: (AId, AId) -> UrgencyEdge -> Doc
printUrgencyEdgePair pair edge =
    let intro = fsep [pfp pair, s2par "introduced because of"]
    in
        fsep [intro, pfp edge]


-- ========================================================================
-- Combined scheduling map

data CSNode = CSN_Sched AId Integer | CSN_Exec AId Integer

-- CSNodes are assigned unique integers to define a total order.  The
-- order allows us to stipulate that nodes for methods order in the
-- same order they appear in the interface and before all nodes for
-- rules, which order according to their introduction in the
-- evaluator.  The number assigned to the Sched and Exec nodes for the
-- same identifier should be identical.
--
-- There are also temporary CSNodes created using qualified Ids.  These
-- temporary CSNodes are all assigned the number -1.  When compared for
-- equality or ordering, they always order after ordinary nodes and
-- order among themselves by the underlying Id.  The Ord instance
-- for temporary nodes is needed to allow the use of sets for performance,
-- but should be only be used in way that will not make the computational
-- result sensitive to the Ord instance on the qualified Ids.
instance Eq CSNode where
  (CSN_Sched i1 n1) == (CSN_Sched i2 n2) =
      if n1 == -1 && n2 == -1
      then i1 == i2 -- temporary CSNodes test against id
      else n1 == n2 -- ordinary nodes test using number (temp /= ordinary)
  (CSN_Exec i1 n1) == (CSN_Exec i2 n2) =
      if n1 == -1 && n2 == -1
      then i1 == i2 -- temporary CSNodes test against id
      else n1 == n2 -- ordinary nodes test using number (temp /= ordinary)
  _ == _ = False -- mixed Sched and Exec are never equal

instance Ord CSNode where
  compare (CSN_Sched i1 n1) (CSN_Sched i2 n2)
      | n1 == -1 && n2 == -1 = compare i1 i2 -- temporary nodes use id order
      | n1 == -1 = GT
      | n2 == -1 = LT
      | otherwise = compare n1 n2 -- ordinary nodes use numeric order
  compare a@(CSN_Exec i1 n1) b@(CSN_Exec i2 n2)
      | n1 == -1 && n2 == -1 = compare i1 i2 -- temporary nodes use id order
      | n1 == -1 = GT
      | n2 == -1 = LT
      | otherwise = compare n1 n2 -- ordinary nodes use numeric order
  compare (CSN_Sched i1 n1) (CSN_Exec i2 n2)
      -- temporary nodes use id order, then Sched < Exec
      | n1 == -1 && n2 == -1 = case (compare i1 i2) of { EQ -> LT; ord -> ord }
      | n1 == -1 = GT
      | n2 == -1 = LT
      -- ordinary nodes use numeric order, then Sched < Exec
      | otherwise =  case (compare n1 n2) of { EQ -> LT; ord -> ord }
  compare (CSN_Exec i1 n1) b@(CSN_Sched i2 n2)
      -- temporary nodes use id order, then Exec > Sched
      | n1 == -1 && n2 == -1 = case (compare i1 i2) of { EQ -> GT; ord -> ord }
      | n1 == -1 = GT
      | n2 == -1 = LT
      -- ordinary nodes use numeric order, then Exec > Sched
      | otherwise = case (compare n1 n2) of { EQ -> GT; ord -> ord }

instance Show CSNode where
  show (CSN_Sched i n) = "CSN_Sched #" ++ (show n) ++ " " ++ (show i)
  show (CSN_Exec  i n) = "CSN_Exec #"  ++ (show n) ++ " " ++ (show i)

instance PPrint CSNode where
    pPrint d p (CSN_Sched i _) = sep [text "CSN_Sched", pPrint d p i]
    pPrint d p (CSN_Exec  i _) = sep [text "CSN_Exec",  pPrint d p i]

data CSEdge = CSE_Urgency UrgencyEdge
            | CSE_Conflict [Conflicts]
            | CSE_SchedBeforeExec
            -- arbitrary earliness is a type of conflict edge
            -- arbitrary urgency is a type of urgency edge

type CSMap = G.GraphMap CSNode CSEdge

printCSEdge :: Bool -> PDetail -> Int -> CSEdge -> Doc
printCSEdge use_pvprint d p edge =
    let pp :: (PVPrint a, PPrint a) => a -> Doc
        pp = if (use_pvprint)
             then pvPrint d 0
             else pPrint d 0
    in  case (edge) of
            (CSE_Urgency uedge) ->
                fsep [s2par "urgency order because of", pp uedge]
            (CSE_Conflict cedge) ->
                fsep [s2par "execution order because of",
                      -- XXX should we display them all?
                      pp (getConflict cedge)]
            (CSE_SchedBeforeExec) ->
                s2par "scheduling of a rule precedes its execution"

instance PPrint CSEdge where
    pPrint d p = printCSEdge False d p

instance PVPrint CSEdge where
    pvPrint d p = printCSEdge True d p


-- This is the actual print used in error messages
printCSEdgePair :: (CSNode, CSNode) -> CSEdge -> Doc
printCSEdgePair (csn1,csn2) edge =
    let pair = (getCSNId csn1, getCSNId csn2)
    in  fsep [pfp pair, pfp edge]

type SchedOrdMap = M.Map AId Integer

mkCSNSched :: SchedOrdMap -> AId -> CSNode
mkCSNSched som i = CSN_Sched i (M.findWithDefault (err i) i som)
  where err aid = internalError $ "Id " ++ (ppReadable aid) ++ " is not in the schedule order map (mkCSNSched)"

mkCSNExec :: SchedOrdMap -> AId -> CSNode
mkCSNExec som i = CSN_Exec i (M.findWithDefault (err i) i som)
  where err aid = internalError $ "Id " ++ (ppReadable aid) ++ " is not in the schedule order map (mkCSNExec)"

-- This creates a CSNExec node without trying to find a unique number
-- for it.  These nodes are for temporary addition to auxiliary
-- graphs (used in reachability analysis through qualified rules),
-- and should not be added into the main graph which assumes a total
-- ordering on all nodes.
mkCSNExec_tmp :: AId -> CSNode
mkCSNExec_tmp i = CSN_Exec i (-1)

getCSNId :: CSNode -> AId
getCSNId (CSN_Sched i _) = i
getCSNId (CSN_Exec  i _) = i

isCSNSched :: CSNode -> Bool
isCSNSched (CSN_Sched _ _) = True
isCSNSched (CSN_Exec  _ _) = False

isCSNExec :: CSNode -> Bool
isCSNExec = not . isCSNSched

-- convert to the external data type
csNodeToSchedNode :: CSNode -> SchedNode
csNodeToSchedNode (CSN_Sched i _) = Sched i
csNodeToSchedNode (CSN_Exec  i _) = Exec i

csGraphToSchedGraph :: [(CSNode,[CSNode])] -> [(SchedNode,[SchedNode])]
csGraphToSchedGraph edges =
    map (\ (i,is) -> (csNodeToSchedNode i, map csNodeToSchedNode is)) edges


-- ========================================================================
-- Monad
--

-- In order to record the warnings during scheduling, we operate on a
-- state monad which stores the EMsgs.

type SM = ExceptT EMsgs (StateT SState IO)

data SState = SState {
                sm_warnings             :: [EMsg],
                sm_method_uses_map      :: Maybe MethodUsesMap,
                sm_rule_uses_map        :: Maybe RuleUsesMap,
                sm_resource_alloc_table :: Maybe RAT,
                sm_exclusive_rules_db   :: Maybe ExclusiveRulesDB,
                sm_sched_order          :: Maybe [SchedNode],
                sm_schedule             :: Maybe ASchedule,
                sm_sched_graph          :: Maybe [(SchedNode, [SchedNode])],
                sm_rule_relation_db     :: Maybe RuleRelationDB,
                sm_v_sched_info         :: Maybe VSchedInfo
              }

initSState :: SState
initSState = SState {
               sm_warnings             = [],
               sm_method_uses_map      = Nothing,
               sm_rule_uses_map        = Nothing,
               sm_resource_alloc_table = Nothing,
               sm_exclusive_rules_db   = Nothing,
               sm_sched_order          = Nothing,
               sm_schedule             = Nothing,
               sm_sched_graph          = Nothing,
               sm_rule_relation_db     = Nothing,
               sm_v_sched_info         = Nothing
             }

addWarnings :: [EMsg] -> SM ()
addWarnings ws = do s <- get
                    let old_ws = sm_warnings s
                    put (s { sm_warnings = old_ws ++ ws })

-- when converting from ErrorMonad, use this function which stores
-- the warnings in addition to reporting them
convEM :: ErrorHandle -> ErrorMonad a -> SM a
convEM errh (EMError emsgs)     = throwError (EMsgs emsgs)
convEM errh (EMWarning wmsgs a) = do addWarnings wmsgs
                                     convIO $ bsWarning errh wmsgs
                                     return a
convEM errh (EMResult a)        = return a

-- for converting from IO
convIO :: IO a -> SM a
convIO = lift . lift

-- ========================================================================
-- The top-level scheduling procedure
--

-- aSchedule
--    flags
--    prefix         - the dir prefix for the source file
--                     (used to output files in the same location)
--    (APackage
--        nm         - package name
--        state      - state elements (Verilog instances)
--        userDefs   - local defs, in dependency-sorted order?
--        userARules - rules, in unspecified order
--        schedPragmas - scheduling relationshops (urgency, preempt)
--        ifs        - interface methods
--    )

-- if scheduling cannot be implemented by Bluesim, then the backend is
-- tainted to be Verilog only, so we return the package with the new backend
aSchedule :: ErrorHandle -> Flags ->
             String -> PathUrgencyPairs -> [PProp] -> APackage ->
             IO (Either AScheduleErrInfo (AScheduleInfo, APackage))
aSchedule errh flags prefix urgency_pairs pps amod = do
    let f = aSchedule' errh flags prefix urgency_pairs pps amod
    (result, s) <- runStateT (runExceptT f) initSState
    let
        processWarning e@(pos,msg) =
            (pos, getErrMsgTag msg, showWarningList [e])
        processError e@(pos,msg) =
            (pos, getErrMsgTag msg, showErrorList [e])
    case result of
        Left msgs ->
            -- if the required fields were not reached, exit with the errors
            case s of
              SState ws (Just mumap) (Just rumap) rat erdb
                        sorder sch sgraph rrdb vsi
                  -> do let
                            schedule_info = AScheduleErrInfo
                                                (map processWarning ws)
                                                (map processError (errmsgs msgs))
                                                mumap rumap rat erdb
                                                sorder sch sgraph rrdb vsi
                        bsErrorNoExit errh (errmsgs msgs)
                        return (Left schedule_info)
              _ -> bsError errh (errmsgs msgs)
        Right amod' ->
            -- All fields should have values
            case s of
              SState ws (Just mumap) (Just rumap) (Just rat) (Just erdb)
                        (Just sorder) (Just sch) (Just sgraph)
                        (Just rrdb) (Just vsi)
                  -> let

                         schedule_info = AScheduleInfo (map processWarning ws)
                                             mumap rumap rat erdb
                                             sorder sch sgraph rrdb vsi
                     in
                         return (Right (schedule_info, amod'))
              _ -> internalError "aSchedule: missing info"


aSchedule' :: ErrorHandle -> Flags ->
              String -> PathUrgencyPairs -> [PProp] -> APackage ->
              SM (APackage)
aSchedule' errh flags prefix urgency_pairs pps amod = do
  tmp1 <- aSchedule_step1 errh flags prefix pps amod
  tmp2 <- aSchedule_step2 errh flags prefix pps urgency_pairs amod tmp1
  aSchedule_step3 errh flags prefix pps amod tmp2

type Step1Output =
    (ConflictMap,
     ConflictMap,
     ConflictMap,
     ConflictMap,
     ConflictMap,
     M.Map RuleId Integer,
     [(ARuleId, [ARuleId])],
     [ARule],
     M.Map ARuleId (Maybe ClockDomain),
     RuleUsesMap,
     ARuleId -> ARuleId -> Bool,
     ARuleId -> ARuleId -> Bool,
     ARuleId -> ARuleId -> Bool,
     S.Set (ARuleId, ARuleId),
     Bool,
     [(RuleId, RuleId, [Conflicts])],
     [(ARuleId, ARuleId, [Conflicts])],
     [(ARuleId, ARuleId, [Conflicts])],
     RuleBetweenMap,
     RuleMethodUseMap,
     [(AId, [ARuleId])],
     Maybe Backend,
     [ADef]
    )

aSchedule_step1 :: ErrorHandle -> Flags -> String -> a -> APackage
                -> SM Step1Output
aSchedule_step1 errh flags prefix pps amod = do
  -- ====================
  -- Definitions

  let nm = apkg_name amod
      gen_backend0 = apkg_backend amod
      state = apkg_state_instances amod
      userDefs = apkg_local_defs amod
      rules_user = (apkg_rules amod)
      schedPragmas = apkg_schedule_pragmas amod
      ifs = apkg_interface amod
  let

      -- Moved this here (from AAddSchedAssumps.hs) because we need to add
      -- new rules and that's messy to do post-scheduling
      (rules_me, orders) = addAllMEAssumps schedPragmas rules_user
      userARules = rules_user ++ rules_me

  let tr s = tracep trace_sched_steps ("aSchedule: " ++ s)

      -- no need to dump DOT files for inlined modules
      dumpDOT = (schedDOT flags) && not (apkg_is_wrapped amod)

      -- definitions of the value methods in the interface
      ifcValueMethods = tr "let ifcValueMethods" $
          [d | (AIDef { aif_value = d }) <- ifs] ++
          [d | (AIActionValue { aif_value = d }) <- ifs]

      -- convert (some) value and (all) action methods into rules
      interfaceRules = tr "let interfaceRules" $ concatMap cvtIfc ifs

      -- create a mapping from the method name to the rule(s) it became
      mutatorMap     = tr "let mutatorMap" $
          [(m, map aRuleName rs) | AIAction {aif_name = m,
                                             aif_body = rs} <- ifs] ++
          [(m, map aRuleName rs) | AIActionValue {aif_name = m,
                                                  aif_body = rs} <- ifs]

      -- non-interface rules
      userRules      = tr "let userRules" $ map cvtARule userARules

      -- group interface and non-interface rules
      rules          = tr "let rules"  $ interfaceRules ++ userRules

      -- group local defs and value methods
      defs           = tr "let defs"   $ ifcValueMethods ++ userDefs

      ruleNames      = tr "let ruleNames"   $ map ruleName rules -- [ARuleId]
      ifcRuleNames   = tr "let ifcRuleNames"  $ map ruleName interfaceRules
      userRuleNames  = tr "let userRuleNames" $ map ruleName userRules

      -- clock domains of rules
      rule_domain_map =
         M.fromList [ (arule_id r, wpClockDomain (arule_wprops r))
                    | r <- userARules
                    ]
      rule_domains =
          mapMaybe (\k -> M.findWithDefault Nothing k rule_domain_map)

  -- create a map from AIds to unique Integers that is used to provide
  -- an ordering for CSNodes.  The ordering is defined so that methods
  -- come first, in the order they appear in the interface (which
  -- should correspond to the order the user wrote them).  After the
  -- methods come the rules, ordered to follow evaluation order within
  -- a module body but to place rules in parent modules before rules
  -- in submodules.
  let num_methods = genericLength ifcRuleNames
      num_total   = num_methods + (genericLength rules_me)
      splitup s = filter (not.null) $ map (dropWhile (=='_')) $ groupBy (\a b -> (b /= '_')) s
      rule_instance r =
          let
              full_name        = splitup (getIdBaseString (aRuleName r))
              full_name_no_suf = init full_name
              full_parts       = length full_name
              rule_name        = splitup (arule_descr r)
              rule_parts       = length rule_name
              n                = full_parts - rule_parts
              (ip1,rp1)        = splitAt n full_name
              (ip2,_)          = splitAt (n-1) full_name_no_suf
          in if (rp1 == rule_name)
             then concat ip1
             else concat ip2
      rule_order (n1,r1) (n2,r2) =
          let i1 = rule_instance r1
              i2 = rule_instance r2
          in if i1 `isPrefixOf` i2
             then LT
             else if i2 `isPrefixOf` i1
                  then GT
                  else n1 `compare` n2
      shuffled_rules = map (aRuleName . snd) $ sortBy rule_order $ zip [num_total..] rules_user
      -- put the me_rules first so they don't get put any later than needed
      sched_id_order = M.fromList $ (zip (ifcRuleNames ++ (map aRuleName rules_me)) [(0::Integer)..]) ++
                                    (zip shuffled_rules [num_total..] )

  -- produce a map of how every rule uses variables and methods
  -- as well as the inverse map about how each method is used
  -- both maps are returned in the SchedInfo for use by later passes
  let (ruleUseMap, methodUseMap, new_defs) =
          tr "let buildUseMaps" $ buildUseMaps defs rules state

  -- add in the new definitions (so we don't have to change code below)
  let defs' = tr "let defs" $ defs ++ new_defs
  let defs = defs'
  let userDefs' = tr "let userDefs" $ userDefs ++ new_defs
  let userDefs = userDefs'

  -- dump ruleUseMap if flagged
  when trace_usemap $ traceM (pp $ sep [text "Rule usemap:",
                                        nest 2 $ pPrint PDDebug 0 ruleUseMap])

  -- dump defs if flagged
  when trace_defs $ traceM $ unlines $ map show defs

  -- dump mutatorMap if flagged
  when trace_mutatormap $ traceM (pp $ sep [text "mutatorMap:",
                                            nest 2 $ pPrint PDDebug 0 mutatorMap])

  -- record the user maps in the state
  s <- get
  put (s { sm_method_uses_map = Just methodUseMap,
           sm_rule_uses_map = Just ruleUseMap })

  when trace_sched_steps $ traceM "defs"

  -- ====================
  -- Scheduling pragmas

  -- check that the Ids in the pragmas refer to actual rules
  -- if not, give an error to the user
  -- (if a compiler bug has led to divergence between the rule names
  -- and ids in the pragmas, then the user will see this message)
  let spids = extractSchedPragmaIds schedPragmas
  let (_ {- goodids -}, badids) = partition (`elem` ruleNames) spids
  when (not (null badids)) $
       convEM errh (errUnknownRules badids)

  -- check that pragmas are not applied across clock domains
  let pragma_domains p = nub $ rule_domains (extractSchedPragmaIds [p])
      bad_pragmas = [ p | p <- schedPragmas, length (pragma_domains p) > 1 ]
      errBadPragma ps = (noPosition, ECrossDomainPragma (map ppString ps))
  when (not (null bad_pragmas)) $
      throwError (EMsgs [errBadPragma bad_pragmas])

  when trace_sched_steps $ traceM "pragmas"

  -- ====================
  -- Disjoint testing (part 1 of 2)

  let
      -- conflict information culled from the ATS:
      --   ncSetCF = no conflict CF set
      --   ncSetSC = no conflict SC set
      --   ncSetPC = no conflict PC set
      --   resMax  = mapping from method name to number of resources available
      (ncSetCF, ncSetPC, ncSetSC, resMax) = tr "let (ncSetCF, ncSetPC, ncSetSC, resMax)" $
          getStateInfo state

      -- rule information used by disjoint testing
      ruletriple = [(ruleName r, rulePred r, ruleAncestor r) | r <- rules]

  -- initial state for rule disjoint testing
  let str = "aschedule_" ++ ppString nm
  disjointState0
      <- convIO $ initDisjointTestState str errh flags defs state ruletriple

  -- dump ncSetCF when flagged
  when trace_ncsets $
      traceM (pp $ sep [text "ncSetCF:", nest 4 $ pPrint PDDebug 0 ncSetCF]
                 $+$ sep [text "ncSetPC:", nest 4 $ pPrint PDDebug 0 ncSetPC]
                 $+$ sep [text "ncSetSC:", nest 4 $ pPrint PDDebug 0 ncSetSC])

  when trace_sched_steps $ traceM "disjoint1"

  -- ====================
  -- Check method uses in a single rule

  -- XXX does this need to be in the middle of the disjoint testing,
  -- XXX or can we merge the two parts and put this checking aftward?

  -- make two maps:
  -- 1. all uses in a rule, sorted by instance
  -- 2. a map of of all method uses in a rule (includes pairs of methods and
  --    single methods which are used multiple times), filtered for only
  --    those pairs (or single methods) which are not parallel composable
  let (ruleMethodUseMap, rulePCConflictUseMap) =
          makeRuleMethodUseMaps ncSetPC ruleUseMap

  -- Check that the actions in a rule are parallel composable.
  -- This may throw an error
  disjointState1 <- verifySafeRuleActions flags userDefs rulePCConflictUseMap disjointState0

  -- make a rule-between-methods map for verifying static schedules
  let ruleBetweenMap = makeRuleBetweenMap state

  -- Check that the actions in a rule can be merged with submodules
  -- to produce a static rule order (if not, taint the .ba file)
  gen_backend1 <- verifyStaticScheduleOneRule errh flags gen_backend0
                      ruleBetweenMap rulePCConflictUseMap

  when trace_sched_steps $ traceM "verifySafeRuleActions"

  -- ====================
  -- Disjoint testing (part 2 of 2)

  let cf_rules_set = S.fromList (extractCFPairsSP schedPragmas)
  let cf_rules_test r1 r2 = ordPair (r1, r2) `S.member` cf_rules_set

  -- determine which rule conditions are disjoint
  (disjoint_set, disjointState2) <-
      convIO $ genDisjointSet disjointState1 (map ruleName rules) schedPragmas

  -- XXX use ordPair to reduce the set size?
  let rule_disjoint r1 r2 = if (r1 == r2)
                            then False
                            else S.member (r1, r2) disjoint_set

  -- XXX ordPair twice
  let cf_or_disjoint r1 r2 = cf_rules_test r1 r2 || rule_disjoint r1 r2

  when trace_sched_steps $ traceM "disjoint2"

  -- ====================
  -- CF conflict graph

      -- Build an initial conflict graph for methods and rules
      -- (containing edges just from conflicting method uses)

      -- The test for method-use conflicts is based on the ncSetCF set,
      -- rule disjoint info, and rule method use map.

  (cfConflictMap0, setToTestForStaticSchedule_cf, disjointState3) <-
      mkConflictMap flags disjointState2
                    ruleMethodUseMap ncSetCF cf_or_disjoint

  -- for better memory performance, force the computation
  deepseq (G.toList cfConflictMap0) $
      when trace_sched_steps $ traceM ("forcing cfConflictMap0")

  -- ====================
  -- PC conflict graph

  let
      -- Produce the PC conflict test in a similar way. The conflict
      -- test passes everything that is passed by cfConflictMap, and
      -- also passes the combinations that are in ncSetPC

      -- convert the cf map into a test
      cf_map_test r1 r2 = isNothing $ G.lookup (r1, r2) cfConflictMap0

  (pcConflictMap0, setToTestForStaticSchedule_pc, disjointState4) <-
      mkConflictMap flags disjointState3
                    ruleMethodUseMap ncSetPC cf_map_test

  -- for better memory performance, force the computation
  deepseq (G.toList pcConflictMap0) $
      when trace_sched_steps $ traceM ("forcing pcConflictMap0")

  -- ====================
  -- SC conflict graph

  let
      -- Produce an SC conflict test based on the ncSetSC,
      -- the CF conflict graph, and rule method use map.
      -- A conflict test is a function from two rule ids to a list
      -- of method pairs between the rules which have the conflict.

      -- (r1,r2) in scConflictMap  <==>  r1 affects something that r2 reads

      -- convert the pc map into a test (XXX why pc?! why not cf?)
      pc_map_test r1 r2 = isNothing $ G.lookup (r1, r2) pcConflictMap0

      -- Using the conflict test, build an initial conflict graph
      -- for methods and rules (just the method conflict edges)
  (scConflictMap0, setToTestForStaticSchedule_sc, disjointState5) <-
      mkConflictMap flags disjointState4
                    ruleMethodUseMap ncSetSC pc_map_test

  -- for better memory performance, force the computation
  deepseq (G.toList scConflictMap0) $
      when trace_sched_steps $ traceM ("forcing scConflictMap0")

  -- ====================

  -- An Action or ActionValue method should be considered to conflict
  -- with itself if it has an argument that is used in the return value
  -- or in the condition of any of the actions.

  let
      -- XXX create new conflict types for these?
      cfConflictEdgesMethodArg =
          tr "let cfConflictEdgesMethodArg" $
          let ds = apkg_local_defs amod
          in  extractMethodArgEdges scConflictMap0 ds ifs
      scConflictEdgesMethodArg =
          tr "let scConflictEdgesMethodArg" $
          -- these are the same edges
          cfConflictEdgesMethodArg
      pcConflictEdgesMethodArg =
          tr "let pcConflictEdgesMethodArg" $
          -- these are the same edges
          cfConflictEdgesMethodArg

  -- Now add the edges to the maps
  let
      cfConflictMap1 = tr "let cfConflictMap1" $
          foldl addConflictEdge cfConflictMap0 cfConflictEdgesMethodArg

      pcConflictMap1 = tr "let pcConflictMap1" $
          foldl addConflictEdge pcConflictMap0 pcConflictEdgesMethodArg

      scConflictMap1 = tr "let scConflictMap1" $
          foldl addConflictEdge scConflictMap0 scConflictEdgesMethodArg

  -- ====================

  -- conflicts introduced by schedPragmas (preempt and any user overrides)
  -- XXX this could probably be done better
  let
      -- for the cf map (edges need to be both directions)
      cfConflictEdgesSP = tr "let cfConflictEdgesSP" $
          extractCFConflictEdgesSP schedPragmas
      -- for the pc map
      pcConflictEdgesSP = tr "let pcConflictEdgesSP" $
          extractPCConflictEdgesSP schedPragmas
      -- for the sc map
      scConflictEdgesSP = tr "let scConflictEdgesSP" $
          extractSCConflictEdgesSP schedPragmas

  -- Now add the edges to the maps
  let
      cfConflictMap = tr "let cfConflictMap" $
          foldl addConflictEdge cfConflictMap1 cfConflictEdgesSP

      pcConflictMap = tr "let pcConflictMap" $
          foldl addConflictEdge pcConflictMap1 pcConflictEdgesSP

      -- (r1,r2) in scConflictMap  <==>  r1 affects something that r2 reads
      scConflictMap = tr "let scConflictMap" $
          foldl addConflictEdge scConflictMap1 scConflictEdgesSP

  -- ====================
  -- For better memory performance, force the computation

  -- XXX Do we need this again, if we already forced the initial maps?
{-
  deepseq (G.toList cfConflictMap) $
      when trace_sched_steps $ traceM ("forcing cfConflictMap")

  deepseq (G.toList pcConflictMap) $
      when trace_sched_steps $ traceM ("forcing pcConflictMap")

  deepseq (G.toList scConflictMap) $
      when trace_sched_steps $ traceM ("forcing scConflictMap")
-}

  -- ====================
  -- Rule Relation DB (1 of 4)

  -- In case an error occurs before all information is gathered,
  -- compute what we know so far about rule relationships, so the user
  -- has at least some info to use for debugging.

  do s <- get
     let rrdb1 = tr "ruleRelationDB" $
                 mkRuleRelationDB ruleNames rule_disjoint
                     cfConflictMap0 scConflictMap0
                     [] [] scConflictEdgesSP []
     put (s { sm_rule_relation_db = Just rrdb1 })

  -- ====================
  -- Resource usage

      -- simultaneous (r1,r2) <==> (r1,r2) might use the same resources
  let simultaneous :: RuleId -> RuleId -> Bool
      simultaneous r r' =
                      (r == r'
                       || isNothing (G.lookup (r,r') cfConflictMap)
                       || isNothing (G.lookup (r,r') scConflictMap)
                       || isNothing (G.lookup (r',r) scConflictMap))
                      -- we assume conflict-free attribute does NOT apply to resource conflicts
                      && (not $ rule_disjoint r r')

      -- check that no method is used by rules in multiple domains
  let method_domain_maps =
        [ M.singleton mid (nub doms, map fst users)
        | (mid, users) <- M.toList methodUseMap
        , (use,(rs1,rs2,_)) <- users
        -- exempt value methods with no arguments, because such methods
        -- can be used in multiple domains (if clocked by no_clock)
        , not (no_arg_valmethod use)
        , let doms = rule_domains (rs1 ++ rs2)
        ]
      no_arg_valmethod (UUExpr (AMethCall {ae_args = []}) _) = True
      no_arg_valmethod _ = False
      add_doms (d1,u1) (d2,u2) = (nub (d1 ++ d2), nub (u1 ++ u2))
      method_domains = M.unionsWith add_doms method_domain_maps
      cross_domain_methods = [ (mid, (doms,us))
                             | (mid, (doms,us)) <- M.toList method_domains
                             , length doms > 1
                             ]
      errCrossDomain (mid, (doms,us)) =
        (getMIdPosition mid,
         ECrossDomainMethodUse (ppString mid)
            [ (ppString u, prPosition (getUUPos u)) | u <- us ])
  when (not (null cross_domain_methods)) $
      throwError (EMsgs (map errCrossDomain cross_domain_methods))

      -- Adjust the the number of copies of a method that are available
      -- to take into account the fact that methods which are composable
      -- which themselves can be used infinitely many times.  In this
      -- table, such a method is given the value 0.
      -- Also consider conflicting methods available infinitely many times
      -- because the schedule resolves that resource conflict
  let resMax' = tr "let resMax'" $ M.fromList
          [(r,n') | let (NoConflictSet pc) = ncSetPC,
                    let (NoConflictSet cf) = ncSetCF,
                    (r,n) <- resMax,
                    -- 0 means all to one port
                    let n' = if ((r,r) `S.member` pc || (r,r) `S.member` cf)
                             then n
                             else 0]

  -- Generate
  --   resAllocTable - the resource allocation table (which will be returned)
  --   resDrops - a list of conflict edges which need to be added to the
  --       conflict graph (or dropped from a no-conflict graph) because
  --       there was a lack of resources to allow the rules to fire in the
  --       same cycle, and the user requested arbitration (via flags)
  (resAllocTable, resDrops) <-
      tr "(resAllocTable, resDrops) <- rSchedule ..." $
      convEM errh $
      rSchedule nm (resource flags) resMax' methodUseMap simultaneous

  -- record the RAT in the state
  s <- get
  put (s { sm_resource_alloc_table = Just resAllocTable })

  -- Converts the triplets in resDrops to conflict edges (in both directions)
  let resDrops' = tr "let resDrops'" $
          concat [ [(r,r',[CResource m]),
                    (r',r,[CResource m])]
                     | (r,r',m) <- resDrops]

      -- cfConflictMap updated with edges for resource arbitration
      cfConflictMapResources = tr "let cfConflictMapResources" $
          foldl addConflictEdge cfConflictMap resDrops'

      -- pcConflictMap updated with edges for resource arbitration
      pcConflictMapResources = tr "let pcConflictMapResources" $
          foldl addConflictEdge pcConflictMap resDrops'

      -- scConflictMap updated with edges for resource arbitration
      scConflictMapResources = tr "let scConflictMapResources" $
          foldl addConflictEdge scConflictMap resDrops'

  -- ====================
  -- Rule Relation DB (2 of 4)

  -- In case an error occurs before all information is gathered,
  -- compute what we know so far about rule relationships, so the user
  -- has at least some info to use for debugging.

  do s <- get
     let rrdb2 = tr "ruleRelationDB" $
                 mkRuleRelationDB ruleNames rule_disjoint
                     cfConflictMap0 scConflictMap0
                     resDrops' [] scConflictEdgesSP []
     put (s { sm_rule_relation_db = Just rrdb2 })

  -- ====================
  -- Final rule-only CF conflict graph

  let
      -- This is the final cfConflictMap
      -- (just an alias for cfConflictMapResources, which has the last
      -- added edges)
      -- This is a graph with rules/methods as vertices and edges for:
      --   method conflicts
      --   sched pragma conflicts
      --   resource arbitration conflicts
      cfConflictMapFinal = tr "let cfConflictMapFinal" $
          cfConflictMapResources


  let dumpConflictMap s m = traceM (pp $ sep [text s,
                                              nest 4 $ pPrint PDReadable 0 m])

  when trace_cfmaps $ do
      dumpConflictMap "CF conflict map 0:" cfConflictMap0
      dumpConflictMap "CF conflict map:" cfConflictMap
      -- cfConflictMapFinal is cfConflictMapResources
  -- dump cfConflictMapFinal if flagged
  when (trace_cfmap  || trace_cfmaps) $
      dumpConflictMap "CF conflict map final:" cfConflictMapFinal

  -- ====================
  -- Final PC conflict graph

  -- pcConflictMapFinal contains all conflicts between methods, that are
  -- called in a single rule. Both pcConflictMapFinal and scConflictMapFinal
  -- are subsets of cfConflictMapFinal, but one of them is not a subset
  -- of the other one in general. One might think that scConflictMapFinal
  -- would be a subset of pcConflictMapFinal, since an SB conflict implies
  -- an SBR conflict. However, scConflictMapFinal also contains conflicts
  -- caused due to cycles. When these maps are used, pcConflictMapFinal is
  -- always consulted after scConflictMapFinal, and if a conflict is found
  -- in scConflictMapFinal then we don't even look for a conflict in
  -- pcConflictMapFinal

  let
      pcConflictMapFinal = tr "let pcConflictMapFinal" $
          pcConflictMapResources

  when trace_pcmaps $ do
      dumpConflictMap "PC conflict map 0:" pcConflictMap0
      dumpConflictMap "PC conflict map:" pcConflictMap
      -- pcConflictMapResources is pcConflictMapFinal

  when (trace_pcmap || trace_pcmaps) $
      dumpConflictMap "PC conflict map final:" pcConflictMapFinal

  -- ====================
  -- Final rule-only SC conflict graph

  -- output DOT file
  when (dumpDOT) $
      convIO $ dumpConflictMapDOT errh flags prefix nm
                                  ifcRuleNames userRuleNames
                                  scConflictMapResources

  let
      -- (r1,r2) in scGraph <==>
      --      r2 must sequence before r1 (if they fire in the same cycle)
      -- scGraph is a list of all rules (r1,r2) where r1 /= r2 and there
      -- is only a conflict from r1 to r2 (and not a conflict the other way)
      scGraph = tr "let scGraph" $
          [(r,[r' | r' <- ruleNames, r' /= r,
                          (r',r) `G.notMember` scConflictMapResources,
                          (r,r') `G.member` scConflictMapResources])
              | r <- ruleNames]

      -- scGraph is going to be used to determine a static global TRS
      -- reference order for simultaneous firing of rules in one cycle.
      -- This will be computed by flattening the scGraph.  Thus, we
      -- have to break any cycles in the scGraph, to insist that one
      -- rule always happens first (even if it could have come second in
      -- some cases).  This sacrifice for a static order is made in
      -- exchange for simpler muxing logic (better area and timing).
      cycleDrops = tr "let cycleDrops" $ drops scGraph

  -- If cycles were broken, warn the user.
  --   This does not need to be let-bound (to take advantage of laziness)
  --   because the drops are needed to compute the query function,
  --   which is always returned.
  when (not (null cycleDrops)) $
      convEM errh (warnCycleDrops nm cycleDrops)

  let
      -- scConflictMapResources updated to be acyclic
      scConflictMapAcyclic = tr "let scConflictMapAcyclic" $
          foldl addConflictEdge scConflictMapResources cycleDrops

      earlinessEdgesMethods = tr "let earlinessEdgesMethods" $
          mkEarlinessEdgesMethods flags ifcRuleNames userRuleNames

      -- scConflictMapAcyclic updated to include earliness order for
      -- methods in relation to rules
      scConflictMapOrder = tr "let scConflictMapOrder" $
          foldl addConflictEdge scConflictMapAcyclic earlinessEdgesMethods

      -- This is the final scConflictMap
      -- (just an alias for scConflictMapOrder, which has the last
      -- added edges)
      -- This is a graph with rules/methods as vertices and edges for:
      --   SC method conflicts
      --   sched pragma conflicts
      --   resource arbitration conflicts
      --   cycles which were broken
      --   earliness restrictions
      --       (currently only method to rule, no user input supported yet)
      scConflictMapFinal = tr "let scConflictMapFinal" $
          scConflictMapOrder

  when trace_scmaps $ do
      dumpConflictMap "SC conflict map 0:" scConflictMap0
      dumpConflictMap "SC conflict map:" scConflictMap
      dumpConflictMap "SC conflict map resources:" scConflictMapResources
      dumpConflictMap "SC conflict map acyclic:" scConflictMapAcyclic
      -- scConflictMapOrder is scConflictMapFinal

  -- dump scConflictMapFinal if flagged
  when (trace_scmap || trace_scmaps) $
      dumpConflictMap "SC conflict map final:" scConflictMapFinal

  -- ====================

  let setToTestForStaticSchedule =
        setToTestForStaticSchedule_cf `S.union`
        setToTestForStaticSchedule_pc `S.union`
        setToTestForStaticSchedule_sc

  -- ====================

  return ( scConflictMap0
         , cfConflictMap0
         , scConflictMapFinal
         , cfConflictMapFinal
         , pcConflictMapFinal
         , sched_id_order
         , orders
         , userARules
         , rule_domain_map
         , ruleUseMap
         , rule_disjoint
         , cf_rules_test
         , cf_or_disjoint
         , setToTestForStaticSchedule
         , dumpDOT
         , resDrops'
         , cycleDrops
         , scConflictEdgesSP
         , ruleBetweenMap
         , ruleMethodUseMap
         , mutatorMap
         , gen_backend1
         , new_defs
         )

-- NOTE: aSchedule' was split into 3 functions because of a memory explosion
--       in GHC. The split was done by duplicating some definitions and passing
--       many values as a huge tuple between them. This was done simply because
--       it was the easiest refactoring technique to apply.

type Step2Output =
    (ConflictMap,
     ConflictMap,
     ConflictMap,
     ConflictMap,
     ConflictMap,
     [AId],
     [AId],
     M.Map ARuleId (Maybe ClockDomain),
     UrgencyMap,
     SchedOrdMap,
     [(ARuleId, [ARuleId])],
     [ARule],
     RuleUsesMap,
     ARuleId -> ARuleId -> Bool,
     ARuleId -> ARuleId -> Bool,
     CSMap,
     [(CSNode, [CSNode])],
     Bool,
     [(ARuleId, ARuleId, [Conflicts])],
     [(ARuleId, ARuleId, [Conflicts])],
     [(ARuleId, ARuleId, [Conflicts])],
     RuleBetweenMap,
     RuleMethodUseMap,
     [(AId, [ARuleId])],
     Maybe Backend,
     [ADef]
    )
aSchedule_step2 :: ErrorHandle -> Flags -> String -> a
                -> [(ARuleId, ARuleId, [PathNode])] -> APackage
                -> Step1Output -> SM Step2Output
aSchedule_step2 errh flags prefix pps urgency_pairs amod ( scConflictMap0
                                                         , cfConflictMap0
                                                         , scConflictMapFinal
                                                         , cfConflictMapFinal
                                                         , pcConflictMapFinal
                                                         , sched_id_order
                                                         , orders
                                                         , userARules
                                                         , rule_domain_map
                                                         , ruleUseMap
                                                         , rule_disjoint
                                                         , cf_rules_test
                                                         , cf_or_disjoint
                                                         , setToTestForStaticSchedule
                                                         , dumpDOT
                                                         , resDrops'
                                                         , cycleDrops
                                                         , scConflictEdgesSP
                                                         , ruleBetweenMap
                                                         , ruleMethodUseMap
                                                         , mutatorMap
                                                         , gen_backend1
                                                         , new_defs
                                                         ) = do
  let tr s = tracep trace_sched_steps ("aSchedule: " ++ s)
      nm = apkg_name amod
      ifs = apkg_interface amod
      schedPragmas = apkg_schedule_pragmas amod
      -- convert (some) value and (all) action methods into rules
      interfaceRules = tr "let interfaceRules" $ concatMap cvtIfc ifs
      ifcRuleNames   = tr "let ifcRuleNames"  $ map ruleName interfaceRules
      userRules      = tr "let userRules" $ map cvtARule userARules
      userRuleNames  = tr "let userRuleNames" $ map ruleName userRules
      -- group interface and non-interface rules
      rules          = tr "let rules"  $ interfaceRules ++ userRules
      ruleNames      = tr "let ruleNames"   $ map ruleName rules -- [ARuleId]

  -- ====================
  -- Rule Relation DB (3 of 4)

  -- In case an error occurs before all information is gathered,
  -- compute what we know so far about rule relationships, so the user
  -- has at least some info to use for debugging.

  do s <- get
     let rrdb3 = tr "ruleRelationDB" $
                 mkRuleRelationDB ruleNames rule_disjoint
                     cfConflictMap0 scConflictMap0
                     resDrops' cycleDrops scConflictEdgesSP []
     put (s { sm_rule_relation_db = Just rrdb3 })

  -- ====================
  -- Rule mutual-exclusion info

  -- database of exclusive rules
  -- XXX the data in cycleDrops, conflictEdgesSP, and resDrops' should
  -- XXX not be needed, because those are in the final maps!
  let exclusive_rules_db =
          mkExclusiveRulesDB ruleNames ruleUseMap
              rule_disjoint cf_rules_test
              cfConflictMapFinal scConflictMapFinal
              resDrops' cycleDrops scConflictEdgesSP

  -- record the db in the state
  s <- get
  put (s { sm_exclusive_rules_db = Just exclusive_rules_db })

  -- ====================
  -- Compute the static TRS reference order within a cycle

  let
      -- scGraphFinal is just like scGraph, but
      --   * it is computed after cycle drops and earliness restrictions
      --     have beed added to the graph,
      --   * it includes all vertices of the graph, not just rules
      --
      -- (r1,r2) in scGraphFinal <==>
      --     r2 must sequence before r1 (if they fire in the same cycle)
      scGraphFinal = tr "let scGraphFinal" $
          [(r,[r' | r' <- G.vertices scConflictMapFinal, r' /= r,
                    (r',r) `G.notMember` scConflictMapFinal,
                    (r,r') `G.member` scConflictMapFinal])
              | r <- G.vertices scConflictMapFinal]

  -- dump scgraphFinal if flagged
  when trace_scgraph $
          traceM (pp $ sep [text "Seq Graph Final:",
                            nest 2 $ pPrint PDReadable 0 scGraphFinal])

  -- output DOT file
  when (dumpDOT) $
      convIO $ dumpExecGraphDOT errh flags prefix nm
                                ifcRuleNames userRuleNames
                                scGraphFinal

  -- This is where we used to compute the flattened earliness order.
  -- Now we combine the earliness and urgency graphs into one,
  -- before flattening.
  -- We do not need to flatten the graph here, looking for cycles,
  -- because cycles in the earliness graph should have already been
  -- handled by cycleDrops.

  -- ====================
  -- Urgency order

  -- Determine the urgency relationships introduced by schedPragmas.
  -- This can return an error if any of the urgency relationships
  -- are trivially reflexive
  urgencyEdgesSP <- tr "urgencyEdgesSP" $
                    convEM errh $
                    extractUrgencyEdgesSP nm schedPragmas

  let
      pathUrgencyEdges = tr "let pathUrgencyEdges" $
          [(rId1, rId2, UEMethodUse path)
              | (rId1, rId2, path) <- urgency_pairs ]

      -- edges for resolving conflicts
      schedUrgencyEdges = urgencyEdgesSP
      -- edges due to data dependency (paths)
      dataUrgencyEdges = pathUrgencyEdges

      -- do not create scheduling edges for urgency relationships that are
      -- trivially satisfied (that is, where there is no conflict, so picking
      -- which rule has priority is not necessary)
      -- (this does not apply to path edges)
      -- (keep the dropped edges in case we need to report warnings)
      (schedUrgencyEdges_filtered, schedUrgencyEdges_dropped) =
          let -- only keep the edges where there *is* a conflict
              rulesConflict (r1, r2, _) =
                  -- it can't be SB in any direction
                  (r1, r2) `G.member` scConflictMapFinal &&
                  (r2, r1) `G.member` scConflictMapFinal
          in  partition rulesConflict schedUrgencyEdges

      urgencyNodes = ruleNames
      urgencyEdges = schedUrgencyEdges_filtered ++ dataUrgencyEdges

      -- XXX if there is an edge for multiple reason, only one reason will
      -- XXX be used in the graph (instead of a list)
      urgencyMap = tr "let urgencyMap" $
                   -- Only make the map with action vertices (no value methods)
                   -- Reverse the ids in an attempt to have the non-ordered
                   -- names appear in the order in which they were given
                   -- (for backwards compatibility with RuleTree).
                   mkUrgencyMap urgencyNodes urgencyEdges

  -- output DOT file (prior to erroring, so this may have cycles)
  when (dumpDOT) $
      convIO $ dumpUrgencyGraphDOT errh flags prefix nm
                                   ifcRuleNames userRuleNames
                                   urgencyMap

  -- This is where we used to compute the flattened urgency order.
  -- Now we combine earliness and urgency graphs into one,
  -- before flattening.
  -- We still flatten the urgency map, though, because we want to detect
  -- cycles.  It is more user-friendly to report cycles as specifically
  -- urgency cycles, than to wait and report cycles in the combined graph.
  _ <- tr "urgency order" $
           convEM errh $
           flattenUrgencyMap nm urgencyMap

  -- trace flag to warn if some user-specified urgencies were not added
  when (trace_no_urgency_edge && not (null schedUrgencyEdges_dropped)) $
      traceM (pp $ sep [text "The following urgency edges were dropped:",
                        nest 2 $ pPrint PDReadable 0
                                     schedUrgencyEdges_dropped])
  -- ====================
  -- Sequentializing scheduling and execution

  let me_pairs = concat (map createArbitraryMEPairs orders)

  -- merge the earliness and urgency graphs
  -- (and return the result as a CSMap and as a list of edges)
  let (seq_map, seq_graph) =
          tr "mkCombinedGraph" $
          mkCombinedGraph ruleNames
              urgencyMap scGraphFinal scConflictMapFinal sched_id_order urgency_pairs me_pairs

  -- output DOT file (prior to erroring, so this may have cycles)
  when (dumpDOT) $
      convIO $ dumpCombinedGraphDOT errh flags prefix nm
                                    ifcRuleNames userRuleNames
                                    seq_graph

  -- dump seq_graph if flagged
  when trace_seqgraph $
          traceM (pp $ sep [text "Seq Graph:",
                            nest 2 $ pPrint PDReadable 0 seq_graph])


  -- make a reachables map, which includes all edges (even through methods)
  seq_reachmap <-
      convIO $ mkReachableMap ifcRuleNames userRuleNames
                              seq_graph sched_id_order

  -- before adding biasing edges, first check whether the combined graph
  -- has any cycles, and report them as errors
  tr "checkCombinedGraphForCycles" $
      checkCombinedGraphForCycles errh nm seq_map seq_graph

  -- now check for dynamic scheduling; this assumes that the graph has no
  -- cycles (thus, the flattening before it) and it returns biasing edges
  -- (thus the flattening after it, this time with the biasing)

  -- check for Bug 1401: that rules/methods, which disjointly call
  -- methods with rules that execute between them, don't have a path in
  -- the schedule graph going in the opposite direction (which would
  -- become a loop when schedules are merged).

  -- we consider rules/methods whose order has not been determined by
  -- consulting all pairs of method calls -- this includes all rules
  -- which are disjoint (or have been made to conflict), but it also
  -- includes any rules where a pair of methods was ignore because the
  -- conditions on those calls were disjoint ("setToTestForStaticSchedule").

  (gen_backend2, implied_edges) <-
      tr "verifyStaticScheduleTwoRules" $
      verifyStaticScheduleTwoRules errh flags gen_backend1 nm
          ruleBetweenMap ruleMethodUseMap ruleNames
          exclusive_rules_db cf_rules_test setToTestForStaticSchedule
          seq_reachmap seq_map seq_graph sched_id_order

  -- the implied edges are only between CF/ME rules so it is OK to add them all
  let seq_graph_implied = addEdgesToCSGraph implied_edges seq_graph
  let seq_map_implied   = foldl G.addWeakEdge seq_map implied_edges

  -- compute the flattened urgency and earliness orders from
  -- the combined graph
  (final_urgency_order, final_reverse_earliness_order, seq_order) <-
      tr "let (final_urgency_order, final_reverse_earliness_order)" $
      do
         -- flatten the combined scheduling graph
         (flattened_order,
          rules_in_urgency_order_seq,
          earliness_order_seq) <-
             flattenCombinedGraph flags nm userRuleNames ifcRuleNames
                 sched_id_order seq_map_implied seq_graph_implied
         return (rules_in_urgency_order_seq,
                 reverse earliness_order_seq,
                 flattened_order)

  -- record the sched order in the state
  s <- get
  put (s { sm_sched_order = Just (map csNodeToSchedNode seq_order) })

  return ( scConflictMap0
         , cfConflictMap0
         , scConflictMapFinal
         , cfConflictMapFinal
         , pcConflictMapFinal
         , final_urgency_order
         , final_reverse_earliness_order
         , rule_domain_map
         , urgencyMap
         , sched_id_order
         , orders
         , userARules
         , ruleUseMap
         , rule_disjoint
         , cf_or_disjoint
         , seq_map
         , seq_graph
         , dumpDOT
         , resDrops'
         , cycleDrops
         , scConflictEdgesSP
         , ruleBetweenMap
         , ruleMethodUseMap
         , mutatorMap
         , gen_backend2
         , new_defs
         )

-- NOTE: aSchedule' was split into 3 functions because of a memory explosion
--       in GHC. The split was done by duplicating some definitions and passing
--       many values as a huge tuple between them. This was done simply because
--       it was the easiest refactoring technique to apply.

aSchedule_step3 :: ErrorHandle -> Flags -> String -> [PProp] -> APackage
                -> Step2Output -> SM APackage
aSchedule_step3 errh flags prefix pps amod ( scConflictMap0
                                           , cfConflictMap0
                                           , scConflictMapFinal
                                           , cfConflictMapFinal
                                           , pcConflictMapFinal
                                           , final_urgency_order
                                           , final_reverse_earliness_order
                                           , rule_domain_map
                                           , urgencyMap
                                           , sched_id_order
                                           , orders
                                           , userARules
                                           , ruleUseMap
                                           , rule_disjoint
                                           , cf_or_disjoint
                                           , seq_map
                                           , seq_graph
                                           , dumpDOT
                                           , resDrops'
                                           , cycleDrops
                                           , scConflictEdgesSP
                                           , ruleBetweenMap
                                           , ruleMethodUseMap
                                           , mutatorMap
                                           , gen_backend2
                                           , new_defs
                                           ) = do

  let tr s = tracep trace_sched_steps ("aSchedule: " ++ s)
      nm = apkg_name amod
      ifs = apkg_interface amod
      state = apkg_state_instances amod
      schedPragmas = apkg_schedule_pragmas amod
      -- convert (some) value and (all) action methods into rules
      interfaceRules = tr "let interfaceRules" $ concatMap cvtIfc ifs
      ifcRuleNames   = tr "let ifcRuleNames"  $ map ruleName interfaceRules
      -- a set, for more efficient lookup
      ifcRuleNamesSet = tr "let ifcRuleNamesSet" $ S.fromList ifcRuleNames
      userRules      = tr "let userRules" $ map cvtARule userARules
      userRuleNames  = tr "let userRuleNames" $ map ruleName userRules
      -- group interface and non-interface rules
      rules          = tr "let rules"  $ interfaceRules ++ userRules
      ruleNames      = tr "let ruleNames"   $ map ruleName rules -- [ARuleId]
      -- non-interface rule assertions (e.g., no-implicit-conditions)
      assertions     = tr "let assertions" $
          [(rId, a) | (ARule rId as _ _ _ _ _ _) <- userARules, a <- as]

  -- ====================
  -- Esposito scheduler

  let
      -- compute the list of rules, in urgency order, paired with the
      -- more urgent rules which conflict (and thus block the rule)
      urgency_conflicts =
          tr "let urgency_conflicts" $
          scheduleEsposito scConflictMapFinal ifcRuleNamesSet final_urgency_order

      schedule = tr "let schedule" $
                 ASchedule [(ASchedEsposito urgency_conflicts)]
                           final_reverse_earliness_order

  -- record the schedule in the state
  s <- get
  put (s { sm_schedule = Just schedule })

  -- ====================
  -- Sanity check -- there should be no conflicts between rules in
  -- different domains.
  let conflict_pairs  = [ ((r1, fromJust d1), (r2, fromJust d2))
                        | (r1,r2s) <- urgency_conflicts
                        , let d1 = M.findWithDefault Nothing r1 rule_domain_map
                        , r2 <- r2s
                        , let d2 = M.findWithDefault Nothing r2 rule_domain_map
                        , (isJust d1) && (isJust d2)
                        ]
      insane_conflicts = filter (\((_,d1),(_,d2)) -> d1 /= d2) conflict_pairs
  when (not (null insane_conflicts)) $
    do let hdr   = "Conflict across clock domains, affecting rules:"
           pairs = [ "  " ++ (getIdString r1) ++ " vs. " ++ (getIdString r2)
                   | ((r1,_),(r2,_)) <- insane_conflicts
                   ]
           msg   = unlines (hdr:pairs)
       internalError msg

  -- ====================
  -- Arbitrary orders

  -- Warn about arbitrary earliness/urgency orders,
  -- and record the decision by adding an edge to the combined graph
  arb_urgency_edges <-
      convEM errh $
      warnAndRecordArbitraryUrgency flags nm urgencyMap urgency_conflicts
          cfConflictMapFinal scConflictMapFinal
          ifcRuleNamesSet sched_id_order userARules

  -- the second list is edges which only result from foreign function
  -- execution order.  since these could be as simple as using $display
  -- in two rules, they are not used to constrain schedinfo (the user
  -- already gets a warning for uses of $display in methods)
  -- we use cf_or_disjoint here even though conflict-free rules have an order
  -- because their order will be enforced by the ME and CF arbitrary edges below
  -- XXX we might miss some ordering warnings this way
  (arb_earliness_edges, arb_earliness_ffunc_edges) <-
      convEM errh $
      warnAndRecordArbitraryEarliness flags nm final_reverse_earliness_order
          cf_or_disjoint ruleUseMap cfConflictMapFinal scConflictMapFinal
          sched_id_order userARules

  -- ====================
  -- We also need to add arbitrary execution order edges for CF and ME rules
  -- because the code used to implement CF and ME assumption-checking
  -- assumes that they will execute in the flattened earliness order
  -- XXX do we ever check that rules are not ME or CF with themselves?

  let rule_order_map = M.fromList (zip final_reverse_earliness_order [(0 :: Integer)..])
  let rule_order_err r = internalError ("ASchedule.hs - not in rule_order_map: " ++ ppReadable r)
  let rule_order_get r = M.findWithDefault (rule_order_err r) r rule_order_map
  let r1_before_r2 r1 r2 = compare (rule_order_get r1) (rule_order_get r2) == GT -- because of reverse order

  let cf_pair_set = S.fromList (extractCFPairsSP schedPragmas)
  let cf_pairs = S.toList (cf_pair_set)

  -- add an edge after each me_check rule (to make it not later than needed)
  let mkMEEdge order (a,_) =
        case (getNextRule a rule_domain_map order) of
           Just r -> [(mkCSNExec sched_id_order a, mkCSNExec sched_id_order r, CSE_Conflict [CArbitraryChoice])]
           _      -> []

  let cf_assump_edges =
         [if r1_before_r2 r1 r2 then
             (mkCSNExec sched_id_order r1, mkCSNExec sched_id_order r2, CSE_Conflict [CArbitraryChoice])
         else
             (mkCSNExec sched_id_order r2, mkCSNExec sched_id_order r1, CSE_Conflict [CArbitraryChoice])
        | (r1, r2) <- cf_pairs]

  let me_and_cf_assump_edges = cf_assump_edges ++ (concat (map (mkMEEdge (reverse final_reverse_earliness_order)) orders))

  -- ====================
  -- Add the edges for recording arbitrary choices

  -- ----------
  -- For the final combined graph
  let
      -- We want to add the following edges to the seq_graph.
      new_map_edges = arb_urgency_edges ++
                      arb_earliness_edges ++ arb_earliness_ffunc_edges ++
                      me_and_cf_assump_edges

      seq_graph_final = addEdgesToCSGraph new_map_edges seq_graph

  -- record the sched graph in the state
  s <- get
  put (s { sm_sched_graph = Just (csGraphToSchedGraph seq_graph_final) })

  -- dump new edges to seq_graph if flagged
  when trace_seqgraph $
          traceM (pp $ sep [text "New Seq Graph Edges:",
                            nest 2 $ pPrint PDReadable 0 new_map_edges])

  when trace_seqgraph $
          traceM (pp $ sep [text "Seq Graph Final:",
                            nest 2 $ pPrint PDReadable 0 seq_graph_final])

  -- ----------
  -- For computing schedInfo

  -- make a version of the map without the ffunc edges,
  -- for computing the schedinfo (but without the ffunc edges,
  -- because $display shouldn't restrict method use)

  -- we also need to make updated versions of the cf/sc/pc conflict maps

  -- we add in the me_and_cf_assump_edges because their ordering
  -- might influence the computed schedInfo (in terms of dynamic scheduling)
  let
      -- in the form (r1,r2) where r1 executes before r2
      new_edges_no_ffunc = arb_urgency_edges ++ arb_earliness_edges
                           ++ me_and_cf_assump_edges

      seq_graph_final_no_ffunc =
          addEdgesToCSGraph new_edges_no_ffunc seq_graph

      -- to force r1 before r2, we add an edge for the conflicting
      -- direction (r2,r1)
      conflict_edges_to_add =
          let convertPair (v1,v2) =
                  (getCSNId v2, getCSNId v1, [CArbitraryChoice])
          in  map (convertPair . fst2of3) new_edges_no_ffunc

      cfMap_with_arb =
          let -- add the edges in both directions
              add_func (v1,v2,e) g =
                  -- XXX use addEdgeWith internalError
                  G.addWeakEdge (G.addWeakEdge g (v1,v2,e)) (v2,v1,e)
          in  foldr add_func cfConflictMapFinal conflict_edges_to_add

      scMap_with_arb =
          let add_func edge graph =
                  -- XXX use addEdgeWith internalError
                  G.addWeakEdge graph edge
          in  foldr add_func scConflictMapFinal conflict_edges_to_add

      -- the pcmap should be unchanged
      pcMap_with_arb = pcConflictMapFinal

  -- ----------
  -- make the combined map too

  -- we need the map, because its edges include an explanation,
  -- so if there's a path found in some of the later checking,
  -- we can use this map to explain the edges along the path
  let seq_map_final_no_ffunc =
          foldl G.addWeakEdge seq_map new_edges_no_ffunc

  -- also, we want to dump it
  -- XXX alternatively, we dump the seq_graph_final and just look up the
  -- XXX new edges in a map
  --
  -- XXX this does not include the ffunc edges, which only exist for
  -- XXX making Verilog and Bluesim try to do tasks in the same order.
  -- XXX We don't warn about those edges, though (do we?), so the user
  -- XXX probably doesn't need them in debugging anyway
  when (dumpDOT) $
      convIO $ dumpCombinedGraphFullDOT errh flags prefix nm
                                        ifcRuleNames userRuleNames
                                        seq_map_final_no_ffunc

  -- ====================
  -- Rule Relation DB (4 of 4)

  -- Now that we have all the information, compute the final RRDB
  -- (for user debug)

  -- - The initial conflict maps are used so that we can show conflicts
  --   just from method calls; other types of conflicts are shown separately
  --   (the edges for these conflicts are passed in as arguments)
  --   XXX note that method-before-rule edges are not passed in,
  --   XXX but that flag is not expected to be used
  -- - the choice of rule_disjoint is deliberate: user conflict_free rules
  --   should show up as CF, possibly with a note, but that is future work
  --
  -- XXX now that the cf/sc maps return multiple conflict explanations,
  -- XXX we should be able to pass just the final cf/sc maps to this function,
  -- XXX in place of the five separate maps/lists of conflicts
  let ruleRelationDB = tr "ruleRelationDB" $
                       mkRuleRelationDB ruleNames rule_disjoint
                           cfConflictMap0 scConflictMap0
                           resDrops' cycleDrops scConflictEdgesSP
                           (arb_earliness_edges ++ arb_earliness_ffunc_edges)

  -- record the db in the state
  s <- get
  put (s { sm_rule_relation_db = Just ruleRelationDB })

  -- Show rule queries,
  -- if the commandline flag was used to request dump of rule relationships
  tr "doQueries" $ convIO $ doQueries errh flags ruleNames ruleRelationDB

  -- ====================
  -- vSchedInfo

  let sub_schedinfo_map = M.fromList [ (avi_vname avi, vSched (avi_vmi avi))
                                     | avi <- state
                                     ]
      method_meth_map = M.fromList [ (r, rumGetMethodIds ruleUseMap r)
                                   | r <- ifcRuleNames
                                   ]

  -- produce SchedInfo on the rules that the ifc methods became
  rSchedInfo <- tr "rSchedInfo" $ convEM errh $
                schedInfo flags nm cfMap_with_arb scMap_with_arb
                    pcMap_with_arb ifcRuleNames userRuleNames
                    sched_id_order ruleBetweenMap ruleMethodUseMap
                    seq_graph_final_no_ffunc
                    sub_schedinfo_map method_meth_map

  let methNames   = map aif_name (aIfaceMethods ifs)
  let rSchedInfo' = addReadyCF pps methNames rSchedInfo

  -- convert SchedInfo on the ifc rules into SchedInfo on the original ifc
  let vSchedInfo = tr "let vSchedInfo" $ fixSchedInfo mutatorMap rSchedInfo'

  -- record the sched info in the state
  s <- get
  put (s { sm_v_sched_info = Just vSchedInfo })

  -- dump vSchedInfo if flagged
  when trace_schedinfo $ do
      traceM (pp $ sep [text "External Scheduling Info:",
                        nest 2 $ pPrint PDReadable 0 vSchedInfo])

  -- ====================

  -- make a reachables map, which includes all edges (even through methods)
  seq_reachmap_no_ffunc <-
      convIO $ mkReachableMap ifcRuleNames userRuleNames
                              seq_graph_final_no_ffunc sched_id_order

  -- check for Bug 1363: that there is no path from a method's Sched node
  -- to its Exec node, except via the direct edge (otherwise, when merging
  -- schedules, the two nodes collapse and a cycle is created)
  when (strictMethodSched flags) $
      checkMethodCycles nm ifcRuleNames
                        seq_reachmap_no_ffunc
                        seq_map_final_no_ffunc
                        sched_id_order

  -- ====================
  -- Verify that rule assertions hold

  let ruleBeforeMap = makeRuleBeforeMap state
      rule_meths = M.fromList [ (rid, rumGetMethodIds ruleUseMap rid)
                              | rid <- ruleNames
                              ]
      sameRule n1 n2 = (getCSNId n1) == (getCSNId n2)
      preds = concat [ map (\x -> (x,[v])) ns'
                     | (v,ns) <- G.toVAList seq_map
                     , let ns' = deleteBy sameRule v ns
                     ]
      pred_map = M.fromListWith (++) preds
      unsyncSet = makeUnsyncSet state

      assertFn = verifyAssertion schedule pred_map ruleBeforeMap
                     unsyncSet rule_meths sched_id_order

  tr "mapM_ verifyAssertion" $
      mapM_ assertFn assertions

  -- ====================
  -- Return

  return (amod { apkg_backend = gen_backend2,
                 apkg_rules = userARules,
                 apkg_local_defs = apkg_local_defs amod ++ new_defs
                })

-- ========================================================================
-- Esposito Scheduler functions
--

--
-- Arguments to scheduleEsposito:
--  cmap      = map of SC conflicts between the rules/methods
--  method_names =
--              ids of the "rules" which are interface methods
--              (used to prevent methods of the same urgency from
--              conflicting for the purpose of computing their WILL_FIRE
--              signals)
--  rs        = rules to be scheduled (in urgency order)
--
scheduleEsposito :: ConflictMap -> S.Set ARuleId -> [ARuleId] ->
                    [(ARuleId, [ARuleId])]
scheduleEsposito cmap_sc method_names rs =
    let
        -- is the "rule" a method
        -- XXX we could avoid a lookup by tagging the Id with a property
        isMethod ruleid = ruleid `S.member` method_names

        -- computes whether two rules conflict for the purposes of scheduling
        -- Note: Conflicting methods which are at the same urgency level
        --   should not have that conflict reflected in the WILL_FIRE signals.
        --   It is reflected in the ifc annotations, leaving the urgency
        --   decision to the caller.
        rulesConflict r1 r2 =
          if isMethod r1 && isMethod r2 then
             False
           else
             (r1,r2) `G.member` cmap_sc &&
             (r2,r1) `G.member` cmap_sc

        foldfunc (res, rs_so_far) r =
            let conflicts = [r' | r' <- rs_so_far, rulesConflict r r']
                res_for_r = (r, conflicts)
            in  (res_for_r:res, r:rs_so_far)

        (conflicts_in_reverse, _) = foldl foldfunc ([], []) rs
    in
        reverse conflicts_in_reverse

-- ========================================================================
-- Warn and record arbitrary earliness/urgency orders
--

-- prettyprint a rule name, dropping RL_ prefix when appropriate
pp_r :: Id -> Doc
pp_r rule = text (pString_r rule)

pString_r :: Id -> String
pString_r rule =
    -- XXX use "dropRulePrefixId"?
    let drop_rule_pfx ('R':'L':'_':rest) = rest
        drop_rule_pfx untouched = untouched
    in  drop_rule_pfx (getIdString rule)

warnAndRecordArbitraryEarliness ::
                 Flags -> AId -> [ARuleId] ->
                 RuleDisjointTest -> RuleUsesMap ->
                 ConflictMap -> ConflictMap -> SchedOrdMap -> [ARule] ->
                 ErrorMonad ([(CSNode,CSNode,CSEdge)],
                             [(CSNode,CSNode,CSEdge)])
warnAndRecordArbitraryEarliness
                 flags moduleId reverse_earliness rule_disjoint rmap
                 cmap_cf cmap_sc sched_id_order user_arules =
    let
        -- find conflicting methods in r1 and r2 which are problematic
        -- if ordered abitrarily.
        conflicting_methods r1 r2 =
            let r1_action_uses = getMethodActionUses (rumGetActionUses rmap r1)
                r2_action_uses = getMethodActionUses (rumGetActionUses rmap r2)
                isActionWithDiffArgs m =
                    case (lookupMethodActionUse m r1_action_uses,
                          lookupMethodActionUse m r2_action_uses) of
                      -- not an Action method
                      (Nothing, Nothing) -> False
                      -- has no arguments
                      (Just ((ACall _ _ (c:es)) : _), Just _) | null es
                          -> False
                      -- otherwise, test whether the arguments can differ
                      -- during simultaneous calls
                      (Just [ACall _ _ (c1:es1)], Just [ACall _ _ (c2:es2)])
                          -> -- if there is only one call, check whether the
                             -- args differ (the conditions don't matter)
                             es1 /= es2
                      (Just uus1, Just uus2)
                          -> -- The optimum test is whether the args differ
                             -- between uses with overlapping conditions,
                             -- however, for simplicity, we just check for
                             -- equality, of conditions and all
                             not (sort uus1 == sort uus2)
                      res -> internalError ("isActionWithDiffArgs: uses: " ++
                                            ppReadable (m, res))
            in case (lookupUseConflict (r1, r2) cmap_cf) of
                 Just (CUse call_pairs) ->
                     let same_calls = [i1 | (i1, i2) <- call_pairs, i1 == i2 ]
                     in filter isActionWithDiffArgs same_calls
                 _ -> []

        -- Given rules r1 and r2, determine whether bsc is making a decision
        -- in choosing which will fire before the other:
        -- earliness is arbitrary if rules are not logically exclusive
        -- and there was a CF conflict but no SC conflict either way
        -- (we don't look for exclusivity, because that was accounted for
        -- in cmap_cf, by removing conflict edges for disjoint rules)
        -- XXX look to make sure a path didn't force the order
        is_earliness_arbitrary r1 r2 =
            (r1, r2) `G.member`    cmap_cf -- CF conflict and
            && (r1, r2) `G.notMember` cmap_sc -- no SC conflict
            && (r2, r1) `G.notMember` cmap_sc -- either way

        no_warn rid = let rs = [i | i <- user_arules, (arule_id i) == rid]
                      in case (rs) of
                                 [r] -> (RPnoWarn `elem` (arule_pragmas r))
                                 _   -> False

        -- produce the warning (only if some method has args)
        warn_earliness_choice r_later r_earlier =
            let pairs = conflicting_methods r_earlier r_later
                affected_method_calls =
                    case (lookupUseConflict (r_earlier, r_later) cmap_cf) of
                      Just c  -> pPrint PDReadable 0 c
                      Nothing -> internalError "warn_earliness_choice: no uses!"
                emsg = WEarlinessChoice
                       { em_more_early = pp_r r_earlier,
                         em_less_early = pp_r r_later,
                         em_conflicts  = affected_method_calls }
            in if ((no_warn r_earlier && no_warn r_later) || null pairs)
               then Nothing
               else Just (getPosition moduleId, emsg)

        -- find the clock domain for a rule
        domain rid = do r <- find (\r -> (arule_id r) == rid) user_arules
                        wpClockDomain (arule_wprops r)

        -- in the absence of having added foreign func edges to the
        -- cfConflict graph to begin with, we check for orders now
        has_task_order r1 r2 =
            -- it has no order (and was not reported as arbitrary)
            isNothing (G.lookup (r1, r2) cmap_cf)
            -- and the reason for CF is not that the rules are exclusive
            && not (rule_disjoint r1 r2)
            -- and there are foreign funcs in both rules
            -- XXX this does not account for disjoint conditions on the ffuncs
            -- XXX nor does it exempt some functions, like $time
            -- XXX nor does it handle the fact that a predicate use
            -- XXX probably ought to imply an urgency edge.
            -- XXX (This can be cleaned up when a better mechanism for
            -- XXX importing ffuncs is added -- that allows indicating which
            -- XXX funcs need to order with others?)
            && rumRuleUsesFF rmap r1
            && rumRuleUsesFF rmap r2
            -- and the rules are in the same clock domain
            && ((domain r1) == (domain r2))

        has_shadowing r1 r2 =
            let sc1 = (r1, r2) `G.member` cmap_sc
                sc2 = (r2, r1) `G.member` cmap_sc
                can_fire_together = (not sc1) || (not sc2)
            in if ((not ((no_warn r1) && (no_warn r2))) && can_fire_together)
               then let affected_calls = conflicting_methods r1 r2
                    in if (null affected_calls)
                       then Nothing
                       else Just (r1, r2, affected_calls)
               else Nothing

        warn_action_shadowing (r_later, r_earlier, ms) =
            (getPosition moduleId,
             WActionShadowing (pString_r r_earlier) (pString_r r_later)
                 (map pfpString ms))

        foldfunc r (edges, ffunc_edges, arb_msgs, shadow_msgs, rs_so_far) =
            let arbs = filter (is_earliness_arbitrary r) rs_so_far
                new_arb_msgs = mapMaybe (warn_earliness_choice r) arbs
                ffunc_arbs = filter (has_task_order r) rs_so_far
                shadows = mapMaybe (has_shadowing r) rs_so_far
                new_shadow_msgs = map warn_action_shadowing shadows
                new_edges =
                    -- r is the later rule, so create an edge that
                    -- says that r2 must execute before r
                    [(mkCSNExec sched_id_order r2, mkCSNExec sched_id_order r, CSE_Conflict [CArbitraryChoice])
                         | r2 <- arbs ]
                new_ffunc_edges =
                    [(mkCSNExec sched_id_order r2, mkCSNExec sched_id_order r, CSE_Conflict [CFFuncArbitraryChoice])
                         | r2 <- ffunc_arbs ]
            in  (new_edges ++ edges,
                 new_ffunc_edges ++ ffunc_edges,
                 new_arb_msgs ++ arb_msgs,
                 new_shadow_msgs ++ shadow_msgs,
                 r:rs_so_far)

        -- this starts with the earliest rule
        (edges, ffunc_edges, arb_msgs, shadow_msgs, _) =
            foldr foldfunc ([],[],[],[],[]) reverse_earliness

        msgs = arb_msgs ++
               if (warnActionShadowing flags) then shadow_msgs else []
    in
        if (null msgs)
        then return (edges, ffunc_edges)
        else EMWarning msgs (edges, ffunc_edges)


warnAndRecordArbitraryUrgency ::
                 Flags -> AId -> UrgencyMap -> [(AId,[AId])] ->
                 ConflictMap -> ConflictMap ->
                 S.Set ARuleId -> SchedOrdMap -> [ARule] -> {- CSMap -> -}
                 ErrorMonad [(CSNode,CSNode,CSEdge)]
warnAndRecordArbitraryUrgency
                 flags moduleId umap urgency_conflicts
                 cmap_cf cmap_sc
                 method_names sched_id_order user_arules {- csmap -} =
    let
        -- is the "rule" a method
        -- XXX we could avoid a lookup by tagging the Id with a property
        isMethod ruleid = ruleid `S.member` method_names

        -- Given rules r1 and r2, where r2 is more urgent than r1,
        -- determine if the order is arbitrary or requested by the user.
        -- The existence of an edge from r2 to r1 means that the
        -- decision was not arbitrary.
        -- XXX look for a path in the csmap, not just an edge
        is_urgency_arbitrary r1 r2 = (r2,r1) `G.notMember` umap

        always_warn rid = let rs = [i | i <- user_arules, (arule_id i) == rid]
                          in case (rs) of
                                 [r] -> (RPwarnAllConflicts `elem` (arule_pragmas r))
                                 _   -> False

        -- If r1 is a rule and r2 is a method, there may not be an edge.
        -- In this case, we bias the rule to be less urgent,
        -- but we don't want to report a warning since we don't allow
        -- the other direction.  (We still need to record these edges.)
        -- XXX When we allow urgency attributes on methods,
        -- XXX we can remove this flag and always warn
        needs_warning r1 r2 =
            if (warnMethodUrgency flags)
            then True
            else (isMethod r1) || (not (isMethod r2))

        -- Given rules r1 and r2 that conflict and for which the urgency
        -- has been chosen to be r2 more-urgent-than r1, determine if
        -- the urgency order is arbitrary and report a warning.
        warn_urgency_choice less_urgent more_urgent =
            let pp_c = pPrint PDReadable 0
                cmap_more_less = G.lookup (more_urgent, less_urgent) cmap_sc
                cmap_less_more = G.lookup (less_urgent, more_urgent) cmap_sc
                info_more_less =
                    case (cmap_more_less :: Maybe [Conflicts]) of
                        Nothing -> empty
                        Just cs ->
                            let -- XXX report multiple reasons?
                                c = getConflict cs
                            in  sep [doubleQuotes (pp_r more_urgent) <+>
                                     text "cannot fire before" <+>
                                     doubleQuotes (pp_r less_urgent) <>
                                     text ":",
                                     nest 2 (pp_c c)]
                info_less_more =
                    case cmap_less_more of
                        Nothing -> empty
                        Just cs ->
                            let -- XXX report multiple reasons?
                                c = getConflict cs
                            in  sep [doubleQuotes (pp_r less_urgent) <+>
                                     text "cannot fire before" <+>
                                     doubleQuotes (pp_r more_urgent) <>
                                     text ":",
                                     nest 2 (pp_c c)]
                emsg = WUrgencyChoice
                         { em_more_urgent = pp_r more_urgent,
                           em_less_urgent = pp_r less_urgent,
                           em_conflicts = (info_more_less $+$
                                           info_less_more) }
            in  (getPosition moduleId,emsg)

        -- reduce the blocking edges to a non-redundant set
        min_conflicts = reduceUrgencyWarnings urgency_conflicts

        should_warn r0 r1 = (is_urgency_arbitrary r0 r1) || (always_warn r0)

        mapfunc (r, blockers) =
            let arbs = filter (should_warn r) blockers
                arbs_to_warn = filter (needs_warning r) arbs
                msgs = map (warn_urgency_choice r) arbs_to_warn
                -- r is the less urgent rule, so create an edge that
                -- says that r2 must schedule before r
                edges = [(mkCSNSched sched_id_order r2, mkCSNSched sched_id_order r,
                          CSE_Urgency UEArbitraryChoice) | r2 <- arbs ]
            in  (edges, msgs)

        (edges, msgs) = concatUnzipMap mapfunc min_conflicts
    in
        if (null msgs || disable_urgency_warnings)
        then return edges
        else EMWarning msgs edges


-- --------------------

reduceUrgencyWarnings :: [(AId, [AId])] -> [(AId, [AId])]
reduceUrgencyWarnings cs =
    let
        -- the rules, in urgency order
        rs = map fst cs
        -- number the rules, to take advantage of the ordering,
        -- and make maps in both directions
        rToNumMap = M.fromList (zip rs [0..])
        numToRMap = M.fromList (zip [0..] rs)
        -- conversion functions
        rToNum r = case (M.lookup r rToNumMap) of
                     Just n -> n
                     Nothing -> internalError ("rToNum: " ++ ppReadable r)
        numToR n = case (M.lookup n numToRMap) of
                     Just r -> r
                     Nothing -> internalError ("numToR: " ++ ppReadable n)
        -- convert the conflicts to numbers
        -- XXX takes advantage of not having to lookup the first rule
        convertToC (r, blockers) n = (n, map rToNum blockers)
        cs' = zipWith convertToC cs [0..]

        -- consider cs' to be a table of rows indicating where there are
        -- direct edges.  now, accumulate the rows, to make a table of which
        -- nodes are reachable from others, and in how many hops
        -- (False indicates one hop, True indicates multiple hops)
        edge_table :: M.Map Int [(Int, Bool)]
        edge_table =
            let findPrevRow n = case (M.lookup n edge_table) of
                                  Just ns -> ns
                                  Nothing -> internalError("findPrevRow: " ++
                                                           ppReadable n)
                f (n, ns) =
                    let one_hops = zip ns (repeat False)
                        mkMultHop n1 = let n2s = findPrevRow n1
                                       in  map (\(i,_) -> (i, True)) n2s
                        mult_hops = concatMap mkMultHop ns
                        ns' = M.toList $
                                  M.fromListWith (||) (one_hops ++ mult_hops)
                    in  (n, ns')
            in  M.fromList $ map f cs'

        -- only keep the edges which indicate that the only path is one hop
        final_cs = let f (n, ns) = let ns' = filter (not . snd) ns
                                   in  (n, map fst ns')
                   in  map f (M.toList edge_table)
        -- convert back to rule names
        convertFromC (n, ns) = (numToR n, map numToR ns)
    in
       map convertFromC final_cs


-- ========================================================================
-- RelaxMethodEarliness utilities
--

-- There are three ways of handling rules vs methods in the execution
-- order ("earliness" order):
--
-- (1) The most conservative method (currently our default) is to
--     enforce that rules always execute after methods.  This is enforced
--     by adding SB relationships from all methods to all rules.
--     Annotations on methods can then be computed pairwise between
--     methods, without consulting the schedule.
--
-- (2) A less conservative method is to allow rules to fall wherever they
--     may, as long as it does not violate the pair-wise method annotations.
--     For instance, a rule cannot fall between two parallel composable
--     methods if the rule would enforce a sequential order on the execution
--     of all three.  This is because any parallel methods have the
--     potential to be call together in one atomic action.  If a rule fired
--     between the methods, the method execution would not be atomic.
--     Another situation to watch for is when a rule sequences between two
--     methods, but in the opposite order that the methods need to sequence.
--     One has to drop cycles in a way that doesn't affect the methods.
--
-- (3) The most free situation is to add no conflicts to the graphs --
--     to allow rules to fall where they may.  And then to compute the
--     method annotations as dictated by the schedule.  So if a rule falls
--     between two parallel methods, those methods become sequenced.
--
-- In situations 2 and 3, we do bias rules to be after methods in the
-- execution order, when either location would work.

mkEarlinessEdgesMethods :: Flags -> [ARuleId] -> [ARuleId] ->
                           [(ARuleId, ARuleId, [Conflicts])]
mkEarlinessEdgesMethods flags ifcRuleNames userRuleNames =
    if (relaxMethodEarliness flags)
    then []
    else -- Methods must execute before rules
         [(u, i, [CMethodsBeforeRules])
             | i <- ifcRuleNames, u <- userRuleNames]


-- ========================================================================
-- Sequentializing the scheduling and execution of rules

-- The "combined" graph is a graph with separate nodes for rule scheduling
-- and rule execution.  It is called "combined" because we create it by
-- combining the urgency and execution graphs.  That is, each node in the
-- urgency graph is considered to be a "scheduling" node and each node in
-- the execution-order graph is considered to be an "execution" node.
-- (Both of these graphs have been checked for cycles, and are therefore
-- known to be acyclic.)  We combine these sets of node and edges, and
-- add edges from the scheduling node of each rule/method to the
-- execution edge of the same rule/method (since scheduling has to happen
-- before execution).  Once the two sets of nodes are joined in this way,
-- we can again look for cycles and report them.

-- XXX The above technique is not correct!
-- Technically, the nodes in the separate urgency and execution-order
-- graphs are representing the ENTIRE rule -- both scheduling and execution.
-- To say that an edge in the execution-order graph is only from execution
-- node to execution node is bogus.  Similarly for the urgency graph.
-- How do we fix this?
-- For execution order:
--   When we analyze what methods are used by a rule, we DO have separate
--   lists of which methods are used in the predicate and which in the body.
--   When we create edges in the conflict map, we treat all uses as an
--   atomic whole.  But we COULD create separate edges in the "combined"
--   graph for uses in the predicate (scheduling) and uses in the body
--   (execution).  It turns out that we're ok leaving the edges as purely
--   being among the execution nodes.  Why?  The scheduling of a rule has
--   to come before its execution, so an edge that says that the execution
--   has to come before another rule is also enforcing that the scheduling
--   has to come before.  The only remaining case is an edge from the
--   execution of rule A to the scheduling of rule B, where currently the
--   edge is to the execution of rule B.  The only uses in rule B's
--   predicate are value methods.  So, given that value methods are
--   always conflict free with value methods, the only way that a method
--   call by rule A can effect rule B is by an action method with a path.
--   This situation we will take care of by adding edges to the combined
--   graph for paths.  It is ok to leave the existing edge (to the rule
--   execution), because an edge to the scheduling node implies an order
--   before the execution.
-- For urgency order:
--   The only problem in the urgency graph is in the accounting for paths
--   (all other edges are legitimately about scheduling order).  But a
--   path is technically implying that execution of rule A must be before
--   the scheduling of rule B -- and this just happens to imply that rule A
--   must be scheduled first, because scheduling of rule A happens before
--   the execution of rule A.  In the separate urgency graph, we just make
--   an edge between scheduling nodes -- for the purpose of detecting cycles
--   and reporting them.  When we create the combined graph, we should
--   correct the edges to be from execution to scheduling.  It is ok to
--   leave the old edge from scheduling to scheduling, since that order is
--   implied by the more correct edges.

-- returns csMap and csGraph
mkCombinedGraph :: [AId] -> UrgencyMap -> [(AId, [AId])] -> ConflictMap ->
                   SchedOrdMap -> PathUrgencyPairs -> [(AId, AId)] ->
                   (CSMap, [(CSNode,[CSNode])])
mkCombinedGraph ruleNames urgencyMap scGraphFinal scConflictMap sched_id_order urgency_pairs me_pairs =
    let
        -- Edges that restrict scheduling of a rule to be prior to
        -- execution of that rule
        s_to_e_edges = [ (mkCSNSched sched_id_order i, mkCSNExec sched_id_order i, CSE_SchedBeforeExec)
                           | i <- ruleNames ]

        -- path edges
        path_edges = [(mkCSNExec sched_id_order rId1, mkCSNSched sched_id_order rId2,
                       CSE_Urgency (UEMethodUse path))
                         | (rId1, rId2, path) <- urgency_pairs ]

        -- convert urgency edges to CSN edges
        mkUrgEdge i1 i2 e@(UEUser _)      =
            (mkCSNSched sched_id_order i1, mkCSNSched sched_id_order i2, CSE_Urgency e)
        mkUrgEdge i1 i2 e@(UEMethodUse _) =
            (mkCSNExec sched_id_order i1, mkCSNSched sched_id_order i2, CSE_Urgency e)
        mkUrgEdge i1 i2 e@(UEArbitraryChoice) =
            (mkCSNSched sched_id_order i1, mkCSNSched sched_id_order i2, CSE_Urgency e)
        urg_edges = [ mkUrgEdge i1 i2 e
                    | (i1,ns) <- G.toList urgencyMap
                    , (i2,e)  <- ns
                    ]

        -- convert sc graph edges to CSN edges
        get_sc_edge pair = fromJustOrErr "mkSeqSchedule: sc lookup"
                               (G.lookup pair scConflictMap)
        early_edges = [ (mkCSNExec sched_id_order i2, mkCSNExec sched_id_order i1, CSE_Conflict e)
                          | (i1,i2s) <- scGraphFinal, -- i2s SB i1
                            i2 <- i2s,
                            let e = get_sc_edge (i1,i2) ]

        me_chk_edges = [ (mkCSNExec sched_id_order r0, mkCSNExec sched_id_order r1, CSE_Conflict [])
                          | (r1,r0) <- me_pairs]

        -- construct a single graph from these edges
        -- (keep the Sched and Exec nodes together, for better ordering
        -- later on)
        nodes = concat [ [mkCSNSched sched_id_order i, mkCSNExec sched_id_order i] | i <- ruleNames ]
        edges = s_to_e_edges ++ path_edges ++ urg_edges ++ early_edges ++ me_chk_edges

        -- as in flattenUrgencyMap, by reversing the edges, we get
        -- the unconstrained edges in the order they appeared in the code
        -- (thus, we don't disrupt the testsuite unnecessarily)
        graph0 = M.fromList [ (n,[]) | n <- nodes ]
        graph  = let edges' = [(i2,[i1]) | (i1,i2,_) <- edges]
                 in  M.toList $ map_insertManyWith (++) edges' graph0

        csmap = mkCSMap nodes edges
    in        --trace ("s_to_e_edges: " ++ ppReadable s_to_e_edges) $
        --trace ("path_edges: " ++ ppReadable path_edges) $
        --trace ("urg_edges: " ++ ppReadable urg_edges) $
        --trace ("early_edges: " ++ ppReadable early_edges) $
        --trace ("Graph: " ++ ppReadable graph) $
        (csmap, graph)

mkCSMap :: [CSNode] -> [(CSNode, CSNode, CSEdge)] -> CSMap
mkCSMap vs es =
    let graph1 = foldl G.addVertex G.empty vs
    in  foldl G.addEdge graph1 es

-- This assumes the edges are not duplicates
-- (which is OK for adding in arbitrary choice edges)
addEdgesToCSGraph :: [(CSNode, CSNode, CSEdge)] ->
                     [(CSNode,[CSNode])] -> [(CSNode,[CSNode])]
addEdgesToCSGraph new_map_edges cs_graph =
  let
      -- seq_graph has no edge type (thus fst2of3) and is in
      -- reverse order (thus swap) for better tsort results.
      -- the edges are also joined by src node (thus joinByFst)
      new_graph_edges = joinByFst (map (swap . fst2of3) new_map_edges)

      -- XXX this looks inefficient
      -- if this is useful, define it in Util.hs
      -- some arbitrary edges may be duplicated, so we fastNub after ++
      addEdges new_es old_es =
          let addEdge :: (Ord a, Ord b) => (a,[b]) -> [(a,[b])] -> [(a,[b])]
              addEdge new_e [] = [new_e]
              addEdge new_e@(k1,vs1) (e@(k2,vs2):es) =
                  if (k1 == k2)
                  then ( (k1, fastNub (vs1 ++ vs2)) : es )
                  else ( e : addEdge new_e es )
          in  foldr addEdge old_es new_es

      new_graph =
          -- if new_edges is null, this will return cs_graph
          addEdges new_graph_edges cs_graph
  in
      new_graph


checkCombinedGraphForCycles :: ErrorHandle ->
                               AId -> CSMap -> [(CSNode,[CSNode])] -> SM ()
checkCombinedGraphForCycles errh moduleId csmap csgraph =
    case (tsort csgraph) of
      Left sccs -> convEM errh $ errCSCycles moduleId csmap sccs
      Right _ -> return ()

-- returns an a flattened ordering of the nodes,
-- as well as an urgency order and an earlines order
flattenCombinedGraph :: Flags -> AId -> [AId] -> [AId] -> SchedOrdMap ->
                        CSMap -> [(CSNode,[CSNode])] ->
                        SM ([CSNode], [AId], [AId])
flattenCombinedGraph flags moduleId userRuleNames ifcRuleNames
                     sched_id_order csmap csgraph =
    -- we assume that cycles in the graph have already been detected
    -- by "checkCombinedGraphForCycle" (and reported in a user-friendly way)
    -- so that we can go ahead and add the bias edges and report an internal
    -- error if a cycle results

    -- Start by sorting the graph and seeing whether biasing is needed
    case (tsort csgraph) of
      Left sccs ->
          internalError ("flattenCombinedGraph 1: " ++ ppReadable sccs)
      Right order1 ->
          let
              ifc_id_set = S.fromList ifcRuleNames
              isMethod node = (getCSNId node) `S.member` ifc_id_set

              (sched_nodes, exec_nodes) = partition isCSNSched order1

              -- walk the order, collecting the bias edges which are known
              -- to be OK (because the rule/method pair appears in that order)
              -- and the candidate bias edges for rule/method pairs that we
              -- want to appear in the opposite order.
              getEdges :: [CSNode] -> ([(CSNode,[CSNode])], [(CSNode, CSNode)])
              getEdges ordered_nodes =
                  let takeFn (es, cs, rules, methods) [] = (es, cs)
                      takeFn (es, cs, rules, methods) (node:ns) =
                          if (isMethod node)
                          then let new_cs = [ (r, node) | r <- rules ]
                                   cs' = new_cs ++ cs
                                   methods' = (node:methods)
                               in  takeFn (es, cs', rules, methods') ns
                          else let new_e = (node, methods)
                                   es' = (new_e:es)
                                   rules' = (node:rules)
                               in  takeFn (es', cs, rules', methods) ns
                  in  takeFn ([], [], [], []) ordered_nodes

              (known_sched_edges, candidate_sched_edges) = getEdges sched_nodes
              (known_exec_edges, candidate_exec_edges) = getEdges exec_nodes

              known_edges = known_sched_edges ++ known_exec_edges
              candidate_edges = candidate_sched_edges ++ candidate_exec_edges

          in
            if (not (biasMethodScheduling flags)) || (null candidate_edges)
            then -- the first order was fine, so return it
                 let urgency_order = map getCSNId sched_nodes
                     earliness_order = map getCSNId exec_nodes
                 in  return (order1, urgency_order, earliness_order)
            else do
              -- add the known edges, to keep those pairs from reverting;
              -- test the candidate edges, to try to bias those orders
              csgraph' <- convIO $
                          addBiasEdgesToCombinedGraph
                              userRuleNames ifcRuleNames sched_id_order csgraph
                              known_edges candidate_edges
              case (tsort csgraph') of
                Left sccs ->
                  internalError ("flattenCombinedGraph 2: " ++ ppReadable sccs)
                Right order2 -> do
                  let (sched_nodes, exec_nodes) = partition isCSNSched order2
                      urgency_order = map getCSNId sched_nodes
                      earliness_order = map getCSNId exec_nodes
                  return (order2, urgency_order, earliness_order)


-- |Add bias edges to a combined scheduling graph.  For any
-- (method,rule) pair that does not already have an ordering
-- relationship, bias edges will be added to the graph to enforce that
-- the method's schedule (execution) node comes before the rule's
-- schedule (execution) node.
addBiasEdgesToCombinedGraph :: [AId]                  -- ^AIds of all rules
                            -> [AId]                  -- ^AIds of methods in the interface
                            -> SchedOrdMap            -- ^map of AIds to CSNode order
                            -> [(CSNode,[CSNode])]    -- ^combined scheduling graph
                            -> [(CSNode,[CSNode])]
                            -> [(CSNode,CSNode)]
                            -> IO [(CSNode,[CSNode])] -- ^combined graph with added edges
addBiasEdgesToCombinedGraph userRuleNames ifcRuleNames sched_id_order csgraph
                            known_bias_edges candidate_bias_edges = do
    let method_ss  = [ mkCSNSched sched_id_order i | i <- ifcRuleNames ]
        rule_ss    = [ mkCSNSched sched_id_order i | i <- userRuleNames ]
        method_es  = [ mkCSNExec  sched_id_order i | i <- ifcRuleNames ]
        rule_es    = [ mkCSNExec  sched_id_order i | i <- userRuleNames ]
        nodes      = method_ss ++ rule_ss ++ method_es ++ rule_es

    -- convert from list representation to map-of-sets
    let edgemap0 = M.fromListWith (S.union) [ (v,S.fromList vs) | (v,vs) <- csgraph ]
        edgemap = let insertFn (v,vs) m = M.insertWith (S.union) v (S.fromList vs) m
                  in  foldr insertFn edgemap0 known_bias_edges
        nodemap = M.fromList [ (v,S.empty) | v <- nodes ]
        old_graph = M.unionWith (S.union) edgemap nodemap

    -- compute information on directed paths between all pairs of nodes
    paths <- computeGraphPaths old_graph

    -- adding the bias edges is implemented as a fold over a path
    -- structure and an accumulator of new edges.
    let maybeAddEdge :: GraphPathInfo CSNode -> M.Map CSNode (S.Set CSNode) -> (CSNode,CSNode) -> IO (M.Map CSNode (S.Set CSNode))
        maybeAddEdge path_info edge_accum (a,b) =
            do a2b <- hasPath path_info a b
               if a2b
                then return edge_accum
                else do b2a <- hasPath path_info b a
                        if b2a
                         then return edge_accum
                         else do addPath path_info a b
                                 return $ M.insertWith S.union a (S.singleton b) edge_accum
    new_edges <- foldM (maybeAddEdge paths) M.empty candidate_bias_edges

    -- add the new edges to the combined graph
    let new_graph = M.unionWith (S.union) old_graph new_edges

    -- convert back to a list-based graph format
    let biased_graph = [ (v,S.toList vset) | (v,vset) <- M.toList new_graph ]

    -- dump seq_graph if flagged
    when trace_seqgraph $
      traceM (pp $ sep [text "Biased Seq Graph:",
                       nest 2 $ pPrint PDReadable 0 biased_graph])
    return (biased_graph)

-- Given a strongly-connected component (SCC) reported by tsort,
-- report an error for the cycle.
-- We'd rather report a cycle to the user, than all edges in an SCC,
-- since a cycle is easier to understand; but we don't want to lose
-- information.  So, we report one cycle from the SCC and mention the
-- other rules which are also intertwined, in case that is helpful to
-- the user.
errCSCycles :: AId -> CSMap -> [[CSNode]] -> ErrorMonad a
errCSCycles moduleId csmap sccs = EMError (map errCSCycle sccs)
  where
    -- report an error for each SCC
    errCSCycle :: [CSNode] -> EMsg
    errCSCycle scc =
        let path = GU.extractOneCycle_gmap csmap scc

            -- the edges along the path
            path_edges = GU.findPathEdges csmap path
            -- remove the SchedBeforeExec edges, because they are not
            -- informative to the user
            path_edges' = filterSchedBeforeExec path_edges
            -- an explanation for each edge
            expl_doc = map (\(p,e) -> printCSEdgePair p e) path_edges'

            -- the names of the nodes in the path (after filtering)
            path_ids = map (getCSNId . fst . fst) path_edges'
            -- report the path such that start and end node are the same
            path_ids' = path_ids ++ [headOrErr "errCSCycle" path_ids]
            path_strs = map pfpString path_ids'

            -- the names of the nodes not in the path, but in the SCC
            other_ids = (nub (map getCSNId scc)) \\ path_ids
            other_strs = map pfpString other_ids
        in
            (getPosition moduleId,
             ECombinedSchedCycle path_strs expl_doc other_strs)

filterSchedBeforeExec :: [((CSNode, CSNode), CSEdge)] ->
                         [((CSNode, CSNode), CSEdge)]
filterSchedBeforeExec path_edges =
        let func ((CSN_Sched i1 _, CSN_Exec i2 _), _) | (i1 == i2) = False
            func _ = True
        in  filter func path_edges

mkPairs :: [[Id]] -> [(Id, Id)]
mkPairs [] = []
mkPairs (ids:idss) = -- trace_answer (\x -> ("mkPairs: " ++ (ppString x)))$
    [(x,y) | x <- ids, y <- concat idss] ++ (mkPairs idss)

mkMEPairs :: [[Id]] -> [([Id], [Id])]
mkMEPairs ([]:rest) = mkMEPairs rest
mkMEPairs [] = []
mkMEPairs (ids:idss) =
    [(ids,y) | y <- idss] ++ (mkMEPairs idss)


extractMEPairsSP :: [ASchedulePragma] -> [([ARuleId],[ARuleId])]
extractMEPairsSP sps =
    let
        mkAllPairs (SPUrgency _) = []
        mkAllPairs (SPExecutionOrder _) = []
        mkAllPairs (SPPreempt _ _) = []
        mkAllPairs (SPSchedule _) = []
        mkAllPairs (SPMutuallyExclusive ids) = mkMEPairs ids
        mkAllPairs (SPConflictFree ids) = []
    in
        nub (map ordPair (concatMap mkAllPairs sps))

extractCFPairsSP :: [ASchedulePragma] -> [(ARuleId,ARuleId)]
extractCFPairsSP sps =
    let
        mkAllPairs (SPUrgency _) = []
        mkAllPairs (SPExecutionOrder _) = []
        mkAllPairs (SPPreempt _ _) = []
        mkAllPairs (SPSchedule _) = []
        mkAllPairs (SPMutuallyExclusive ids) = []
        mkAllPairs (SPConflictFree ids) = mkPairs ids
    in
        nub (map ordPair (concatMap mkAllPairs sps))

createArbitraryMEPairs :: (ARuleId, [ARuleId]) -> [(ARuleId,ARuleId)]
createArbitraryMEPairs (nid, aids) =
    let mkPair a = (nid, a)
    in map mkPair aids


-- ========================================================================
-- SchedulePragma utilities
--

extractCFConflictEdgesSP :: [ASchedulePragma] -> [(ARuleId,ARuleId,[Conflicts])]
extractCFConflictEdgesSP sps =
    let
        mkEdges (SPUrgency _) = []
        mkEdges (SPExecutionOrder ids) =
            ([ edge | id1 <- ids, id2 <- ids, id1 /= id2,
                      let pos = getPosition id1,
                      edge <- [(id1, id2, [CUserEarliness pos]),
                               (id2, id1, [CUserEarliness pos])]])
        mkEdges (SPMutuallyExclusive _) = []
        mkEdges (SPConflictFree _) = []
        mkEdges (SPPreempt ids1 ids2) =
            ([ edge | id1 <- ids1,
                      let pos = getPosition id1,
                      id2 <- ids2,
                      edge <- [(id1, id2, [CUserPreempt pos]),
                               (id2, id1, [CUserPreempt pos])]])
        -- Handle user overrides:
        --    The user can add conflicts with SB, SBR, or C.
        --    For the CFMap, edges run both directions.
        mkEdges (SPSchedule s) =
            concat [ [(x,y,[CUserAttribute pos]),
                      (y,x,[CUserAttribute pos])]
                       | (x,y) <- (sSB  s) ++ (sSBR s) ++ (sC s),
                         let pos = getPosition x ]
    in
     concatMap mkEdges sps

extractPCConflictEdgesSP :: [ASchedulePragma] -> [(ARuleId,ARuleId,[Conflicts])]
extractPCConflictEdgesSP sps =
    let
        mkEdges (SPUrgency _) = []
        mkEdges (SPExecutionOrder ids) =
            ([ edge | id1 <- ids, id2 <- ids, id1 /= id2,
                      let pos = getPosition id1,
                      edge <- [(id1, id2, [CUserEarliness pos]),
                               (id2, id1, [CUserEarliness pos])]])
        mkEdges (SPMutuallyExclusive _) = []
        mkEdges (SPConflictFree _) = []
        mkEdges (SPPreempt ids1 ids2) =
            ([ edge | id1 <- ids1,
                      let pos = getPosition id1,
                      id2 <- ids2,
                      edge <- [(id1, id2, [CUserPreempt pos]),
                               (id2, id1, [CUserPreempt pos])]])
        -- Handle user overrides:
        --    The user can add conflicts with SB, SBR, or C.
        mkEdges (SPSchedule s) =
            concat [ [(x,y,[CUserAttribute pos]),
                      (y,x,[CUserAttribute pos])]
                       | (x,y) <- (sSBR s) ++ (sC s),
                         let pos = getPosition x ]
    in
     concatMap mkEdges sps

extractSCConflictEdgesSP :: [ASchedulePragma] -> [(ARuleId,ARuleId,[Conflicts])]
extractSCConflictEdgesSP sps =
    let
        mkEdges (SPUrgency _) = []
        mkEdges (SPExecutionOrder ids) =
            let mkE i1 i2 = (i2, i1, [CUserEarliness (getPosition i1)])
                mkEs [] = []
                mkEs (i1:is) = (map (\i2 -> mkE i1 i2) is) ++ (mkEs is)
            in  mkEs ids
        mkEdges (SPMutuallyExclusive _) = []
        mkEdges (SPConflictFree _) = []
        mkEdges (SPPreempt ids1 ids2) =
            ([ edge | id1 <- ids1,
                      let pos = getPosition id1,
                      id2 <- ids2,
                      edge <- [(id1, id2, [CUserPreempt pos]),
                               (id2, id1, [CUserPreempt pos])]])
        -- Handle user overrides:
        --    The user can add conflicts with SB, SBR, or C.
        mkEdges (SPSchedule s) =
            [ (x,y,[CUserAttribute pos])
                | (x,y) <- (sSB  s) ++ (sSBR s),
                  let pos = getPosition x ] ++
            concat [ [(x,y,[CUserAttribute pos]),
                      (y,x,[CUserAttribute pos])]
                       | (x,y) <- (sC s),
                         let pos = getPosition x ]
    in
     concatMap mkEdges sps


extractUrgencyEdgesSP :: Id -> [ASchedulePragma] ->
                         ErrorMonad [(ARuleId,ARuleId,UrgencyEdge)]
extractUrgencyEdgesSP nm sps =
    let
        mkEdge id1 id2 = (id1, id2, UEUser [getPosition id1, getPosition id2])

        mkEdges [] = []
        mkEdges (id1:ids) =
            (map (\id2 -> mkEdge id1 id2) ids) ++ (mkEdges ids)

        -- returns a list of edges for one pragma
        handleSP :: ASchedulePragma -> [(ARuleId,ARuleId,UrgencyEdge)]
        handleSP (SPUrgency ids) = mkEdges ids
        handleSP (SPPreempt ids1 ids2) = [ mkEdge id1 id2
                                               | id1 <- ids1, id2 <- ids2 ]
        -- the other pragmas have no affect on urgency
        handleSP (SPExecutionOrder _) = []
        handleSP (SPSchedule _) = []
        handleSP (SPMutuallyExclusive _) = []
        handleSP (SPConflictFree _) = []

        edges = concatMap handleSP sps

        isReflexiveEdge (i1,i2,_) = (i1 == i2)
        reflexive_edges = filter isReflexiveEdge edges
    in
        do
           when (not (null reflexive_edges)) $
               errReflexiveUserUrgency reflexive_edges
           return edges


errUnknownRules :: [Id] -> ErrorMonad ()
errUnknownRules rs =
    let errUnknownRule rId = (getPosition rId, EUnknownRuleId  (pfpString rId))
    in  EMError (map errUnknownRule rs)


errReflexiveUserUrgency :: [(ARuleId,ARuleId,UrgencyEdge)] -> ErrorMonad a
errReflexiveUserUrgency es =
    let mkEMsg (i1,i2,_) = (noPosition,
                            EReflexiveUserUrgency (pfpString i1)
                                (getPosition i1) (getPosition i2))
    in  EMError (map mkEMsg es)


-- ========================================================================
-- Compute conflict edges for action methods with themselves
-- when use of an argument (in conditions or return values)
-- limits the method to conflict with itself (not be SC)

extractMethodArgEdges :: ConflictMap -> [ADef] -> [AIFace] ->
                         [(ARuleId,ARuleId,[Conflicts])]
extractMethodArgEdges scConflictMap0 ds ifs =
  let
      -- Construct (lazily and recursively) a map from each def to the
      -- set of module ports that it uses.
      port_usemap = M.fromList (map findDefPortUses ds)

      findExprPortUses e =
          let accumFn (ASPort _ i) pmap = S.insert i pmap
              accumFn (ASDef _ i) pmap =
                  -- recursive construction
                  case (M.lookup i port_usemap) of
                    Nothing -> internalError ("port_usemap: " ++ ppReadable i)
                    Just m -> S.union m pmap
              accumFn _ pmap = pmap
          in  exprFold accumFn S.empty e

      findDefPortUses (ADef di _ de _) = (di, findExprPortUses de)

      -- ActionValue methods with arguments should be considered to
      -- conflict with themselves if the return value uses an argument
      --
      findAVValueUses :: ADef -> S.Set AId
      findAVValueUses = snd . findDefPortUses

      -- Action/ActionValue methods with arguments should be considered
      -- to conflict with themselves if any action call condition uses
      -- an argument
      --
      findACondUses :: [ARule] -> S.Set AId
      findACondUses rs =
          let getCond = headOrErr "findACondUses: getCond"
              findActionPortUses :: AAction -> S.Set AId
              findActionPortUses = findExprPortUses . getCond . aact_args
              findRulePortUses :: ARule -> S.Set AId
              findRulePortUses = S.unions . map findActionPortUses . arule_actions
          in  S.unions $ map findRulePortUses rs

      -- Given an interface field, determine if a conflict edge is needed
      findAIFaceUses (AIActionValue { aif_name = mid,
                                      aif_value = d,
                                      aif_body = rs,
                                      aif_inputs = as }) =
          -- If the edge already exists, don't bother
          if G.member (mid, mid) scConflictMap0
          then S.empty
          else let argset = S.fromList (map fst as)
                   condset = findACondUses rs
                   valset = findAVValueUses d
               in  S.intersection argset (S.union condset valset)
      findAIFaceUses (AIAction { aif_name = mid,
                                 aif_body = rs,
                                 aif_inputs = as }) =
          -- If the edge already exists, don't bother
          if G.member (mid, mid) scConflictMap0
          then S.empty
          else let argset = S.fromList (map fst as)
                   condset = findACondUses rs
               in  S.intersection argset condset
      findAIFaceUses _ = S.empty

  in
     [ (mid, mid, [CUse uses])
     | ifc <- ifs,
       let mid = aif_name ifc,
       let arg_uses = findAIFaceUses ifc,
       not (S.null arg_uses),
       let mkUse a = (MethodId emptyId a, MethodId emptyId a),
       let uses = map mkUse (S.toList arg_uses) ]


-- ========================================================================
-- Disjoint testing
--

-- retrieve conflict information from ATS
getStateInfo :: [AVInst] ->
                (NoConflictSet, NoConflictSet, NoConflictSet, [(MethodId,Integer)])
getStateInfo ss = (NoConflictSet $ S.unions cfss,
                   NoConflictSet $ S.unions pcss,
                   NoConflictSet $ S.unions scss,
                   rss)
    where cfss = [cfs  | (cfs, _, _, _) <- sinfos]
          pcss = [sbs  | (_, sbs, _, _) <- sinfos]
          scss = [sbrs | (_, _,sbrs, _) <- sinfos]
          rss  = sort $ concat [r  | (_, _, _, r)  <- sinfos]
          sinfos = map getSI ss
          getSI (AVInst { avi_vname = id, avi_vmi = modInfo }) =
              (cfs, sbs, sbrs, [(MethodId id mid, use) | (mid,use) <- rs])
              where mci = methodConflictInfo (vSched modInfo)
                    cfs = S.fromList $ concat
                          [[(m1, m2), (m2, m1)]
                           | (mn1, mn2) <- sCF mci,
                           let m1 = MethodId id mn1, let m2 = MethodId id mn2]

                    sbs = cfs `S.union`
                              S.fromList [(MethodId id m1, MethodId id m2)
                                            | (m1, m2) <- sSB mci]

                    sbrs = sbs `S.union`
                              S.fromList [(MethodId id m1, MethodId id m2)
                                            | (m1, m2) <- sSBR mci]

                    rs = sort [(m, n) | Method { vf_name = m, vf_mult = n } <- vFields modInfo]

-- ========================================================================
-- vSchedInfo
--

-- This function generates the external scheduling info (the annotations)
-- for interface methods (for all ifcRuleNames).
--
-- This gets slightly tricky when we allow rules to intermingle with
-- methods, because two methods which might otherwise have been CF might
-- become SB because of a rule which has to order in between them.
-- We don't have to worry about two methods which are SB in one direction
-- having a rule which sequences between the two in the other direction,
-- because cycle dropping will have caught that.
--
-- Thus, the algorithm is this:  Use the same algorithm as before, for
-- finding pairwise relationships between methods by consulting only the
-- edges between those methods in the conflict graphs ... and if that
-- information says that the methods are conflict free, then do a second
-- check to see if an intermediate rule has changed that.  And if so,
-- we change the annotation.  We don't issue a warning about this, except
-- when a trace flag is on, because it's only interesting to developers.
--
-- Note that in revision 2894, Lennart rewrote the basic algorithm into
-- two loops (and outer and an inner) to speed up computation.

schedInfo :: Flags -> AId -> ConflictMap -> ConflictMap -> ConflictMap ->
             [ARuleId] -> [ARuleId] -> SchedOrdMap ->
             RuleBetweenMap -> RuleMethodUseMap -> [(CSNode, [CSNode])] ->
             M.Map AId VSchedInfo -> M.Map AId [MethodId] ->
             ErrorMonad VSchedInfo
schedInfo flags moduleId cfmap scmap pcmap
          ifcRuleNames userRuleNames sched_id_order
          ruleBetweenMap ruleMethodUseMap seq_graph
          sub_schedinfo_map method_meth_map =
  let
      -- -----

      -- outer loop:
      --   For each rule, no need to check it against all N other rules if
      --   there are no edges to other rules in the cfmap.  If there are
      --   edges, only check in the SC map for rules which have edges
      --   (are not conflicting)
      --   We avoid duplicates by only generating pairs between a rule and
      --   the rules that follow it.
      outer :: [(ARuleId, ARuleId)] ->
               [(ARuleId, ARuleId)] ->
               [(ARuleId, ARuleId)] ->
               [(ARuleId, ARuleId)] ->
               [WMsg] ->
               [ARuleId] ->
                   ([(ARuleId, ARuleId)],
                    [(ARuleId, ARuleId)],
                    [(ARuleId, ARuleId)],
                    [(ARuleId, ARuleId)],
                    [WMsg])

      outer cf sb sbr conf wmsgs [] = (cf,sb,sbr,conf,wmsgs)
      outer cf sb sbr conf wmsgs (r:rs) =
          case G.getOutEdgeMap cfmap r of
              -- If no rule conflicts with r, add (r,r') to the list of
              -- conflict free rules for all r'
              Nothing ->
                  -- avoid duplicates by only using "rs" (include "r" itself)
                  let new_cf = [(r, r') | r' <- (r:rs)]
                  in  outer (new_cf ++ cf) sb sbr conf wmsgs rs
              -- If there are rules that conflict with r, go through all rules
              Just cfEdgemap ->
                  -- avoid duplicates by only using "rs" (include "r" itself)
                  inner cf sb sbr conf wmsgs (r:rs)
                where
                  -- inner loop:
                  --   Determine this rule's relationship with each
                  --   remaining rule
                  inner cf sb sbr conf wmsgs [] = outer cf sb sbr conf wmsgs rs
                  inner cf sb sbr conf wmsgs (r':rs') =
                    let
                        -- if we've determined that there's an SC conflict in one
                        -- direction (r1 to r2), but not the other, then we use
                        -- this function to determine if the relation is SB or SBR
                        doSB pcmap r1 r2 =
                            -- PC map is not reflexive, so use the right one
                            case (pcmap >>= M.lookup r2) of
                              -- There is no PC conflict
                              -- so the rules are (r1 SB r2)
                              Nothing ->
                                  -- but change to SBR if there's a rule between
                                  let (sb2, sbr2, wmsgs2) =
                                          changeSBToSBR (r1,r2) sb sbr wmsgs
                                  in  (sb2, sbr2, conf, wmsgs2)
                              -- There is a PC conflict
                              -- so the rules are (r1 SBR r2)
                              Just _ -> (sb, (r1,r2):sbr, conf, wmsgs)
                    in
                    case (M.lookup r' cfEdgemap) of
                      -- the rules are CF
                      Nothing ->
                          -- but change to SBR if there's a rule between
                          let (cf', sbr', wmsgs') =
                                  changeCFToSBR (r,r') cf sbr wmsgs
                          in  inner cf' sb sbr' conf wmsgs' rs'
                      -- the rules are not CF
                      Just _ ->
                          let (sb', sbr', conf', wmsgs') =
                                  case (mSCEdgeMap >>= M.lookup r') of
                                    -- There is no SC conflict from r to r'
                                    -- (there must be a conflict the other way,
                                    -- because otherwise they'd be CF)
                                    Nothing -> doSB mPCEdgeMap r r'
                                    -- There is a SC conflict from r to r'
                                    Just _ ->
                                        case (G.getOutEdgeMap scmap r' >>= M.lookup r) of
                                          -- There is no SC conflict from r' to r
                                          Nothing -> doSB (G.getOutEdgeMap pcmap r') r' r
                                          -- There is a SC conflict from r' to r
                                          -- so the rules are (r C r')
                                          Just _  -> (sb, sbr, (r,r'):conf, wmsgs)
                          in inner cf sb' sbr' conf' wmsgs' rs'

                  mSCEdgeMap = G.getOutEdgeMap scmap r
                  mPCEdgeMap = G.getOutEdgeMap pcmap r

      -- -----

      -- Function to determine whether there is a path in the combined
      -- scheduling graph from the execution of one method to the
      -- execution of another method with rules in between (thus enforcing
      -- an order).

      -- this is returned in SchedInfo
      hasRulePairs :: [ ((ARuleId, ARuleId), [ARuleId]) ]
      hasRuleBefore :: [ (ARuleId, [Either ARuleId AMethodId]) ]
      (hasRulePairs, hasRuleBefore) =
          findRuleBetweenAndBeforeMethods flags ifcRuleNames userRuleNames
              ruleBetweenMap ruleMethodUseMap sched_id_order
              seq_graph sub_schedinfo_map method_meth_map

      unsyncMethods :: [ARuleId]
      unsyncMethods = findUnsyncMethods ifcRuleNames
                                        sub_schedinfo_map method_meth_map

      -- this is used for lookup when computing MethodConflictInfo
      hasRuleMap :: M.Map (ARuleId, ARuleId) [ARuleId]
      hasRuleMap = M.fromList hasRulePairs

      -- -----

      -- construct a warning that the CF annotation is changed to SB
      -- due to a graph path
      warnChange m1 m2 path =
          (getPosition moduleId,
           WMethodAnnotChange (pfpString m1) (pfpString m2)
               (map pfpString path))

      -- Given a pair of methods determined to be CF or SB with each other,
      -- figure out if they are actually SBR because of intermediate rules.
      -- Returns the CF/SB pairs and the SBR pairs and the warnings,
      -- after adding the new pair appropriately.
      -- For SB methods, we only need to look up in that direction.
      -- XXX For CF methods, we only need to look up in the flattened rule
      -- XXX order direction.  But we seem to be OK with efficiency for now.
      changeCFOrSBToSBR :: Bool -> (AId, AId) ->
                           [(AId, AId)] -> [(AId, AId)] -> [WMsg] ->
                           ([(AId, AId)], [(AId, AId)], [WMsg])
      changeCFOrSBToSBR isCF (meth1, meth2) cf_or_sbs sbrs wmsgs =
          let dflt_res = ((meth1,meth2):cf_or_sbs, sbrs, wmsgs)
              sbr_res m1 m2 path =
                  let wmsg = warnChange m1 m2 path
                  in  (cf_or_sbs, (m1,m2):sbrs, wmsg:wmsgs)
          in  case (M.lookup (meth1,meth2) hasRuleMap) of
                Just path -> sbr_res meth1 meth2 path
                Nothing -> if isCF
                           then case (M.lookup (meth2,meth1) hasRuleMap) of
                                  Just path -> sbr_res meth2 meth1 path
                                  Nothing -> dflt_res
                           else dflt_res

      changeCFToSBR = changeCFOrSBToSBR True
      changeSBToSBR = changeCFOrSBToSBR False

      -- -----

      -- Put it all together

      (cf,sb,sbr,conf,wmsgs) = outer [] [] [] [] [] ifcRuleNames
      mci = MethodConflictInfo {
                sCF  = cf,
                sSB  = sb,
                sSBR = sbr,
                sC   = conf,
                sME  = [],
                sP   = [],
                sEXT = []
            }
      res = SchedInfo mci hasRulePairs hasRuleBefore unsyncMethods
  in
      if trace_schedinfo && not (null wmsgs)
      then EMWarning wmsgs res
      else EMResult res

-- --------------------

-- Rule(s) between methods, rule(s) before methods

-- This function returns two sets of data:
-- * Pairs of methods for which there is a rule (or rules) which must execute
--   between them (specifically, there is a path in the combined scheduling
--   graph from the execution of one method to the execution of another,
--   passing through rules), and the names of the rules
-- * Methods which have a rule (or rules) that must execute before the method

-- These are done in the same function because they share the same
-- data: the reachability graph from rules to methods.

-- For rules between methods:
-- (Paths through other methods are not considered, because they only
-- matter if that method is called, in which case the pairwise
-- annotations with that method will be considered.  If just the outer
-- methods are used, they should not be restricted.)

-- Approach: Construct the forward graph with no outgoing edges from
-- any method and compute reachables to methods from each rule.  Then,
-- for each method pair, check if any of the outgoing rules from
-- the execution node of m1 can reach m2 (the exec node, but if it can
-- reach the scheduling node, it can also reach the exec node).

-- An alternative might be: Make a graph of just the rules and compute
-- the pairs (r,rs) where rs are reachable from r.  For each method,
-- make a list of outgoing and ingoing edges (to rules only).  Take
-- the outgoing rs from m1, find the union of their reachable rules,
-- and test if any of those are in the ingoing rules to m2.

findRuleBetweenAndBeforeMethods
    :: Flags -> [ARuleId] -> [ARuleId] ->
       RuleBetweenMap -> RuleMethodUseMap -> SchedOrdMap ->
       [(CSNode, [CSNode])] ->
       M.Map AId VSchedInfo -> M.Map AId [MethodId] ->
       ([((ARuleId, ARuleId), [ARuleId])],
        [(ARuleId, [Either ARuleId AMethodId])])
findRuleBetweenAndBeforeMethods flags ifcRuleNames userRuleNames
                                ruleBetweenMap ruleMethodUseMap sched_id_order
                                seq_graph sub_schedinfo_map method_meth_map =
  let
      (reachable_meth_map, meth_outgoing_edges_map) =
          makeRuleMethodReachableMaps flags ifcRuleNames userRuleNames
                                      ruleBetweenMap ruleMethodUseMap
                                      sched_id_order seq_graph

      hasRuleBetween =
          findRuleBetweenMethods ifcRuleNames
                                 meth_outgoing_edges_map reachable_meth_map

      hasRuleBefore =
          findRuleBeforeMethods ifcRuleNames userRuleNames
                                sub_schedinfo_map method_meth_map
                                reachable_meth_map
  in (hasRuleBetween, hasRuleBefore)


makeRuleMethodReachableMaps
    :: Flags -> [ARuleId] -> [ARuleId] ->
       RuleBetweenMap -> RuleMethodUseMap -> SchedOrdMap -> [(CSNode, [CSNode])] ->
       (M.Map CSNode [(AId, [CSNode])], M.Map AId [CSNode])
makeRuleMethodReachableMaps flags ifcRuleNames userRuleNames
                            ruleBetweenMap ruleMethodUseMap sched_id_order seq_graph =
  let
      all_ids = ifcRuleNames ++ userRuleNames

      -- add rules and edges to graph to represent paths through submodule
      -- method calls (where there is a rule between the methods)
      (rb_nodes, rb_edges) =
          makeRuleBetweenEdges ruleBetweenMap ruleMethodUseMap all_ids sched_id_order

      seq_s_nodes, seq_e_nodes, seq_nodes :: [CSNode]
      seq_s_nodes = [ mkCSNSched sched_id_order i | i <- all_ids ]
      seq_e_nodes = [ mkCSNExec  sched_id_order i | i <- all_ids ]
      seq_nodes = seq_s_nodes ++ seq_e_nodes ++ rb_nodes

      -- for efficiency of lookup, make the ifc names a set
      ifc_id_set = S.fromList ifcRuleNames
      isMethodId i = i `S.member` ifc_id_set

      -- the edges of seq_graph expressed individually
      -- (reversed to put them in SB order: (n1,n2) => n1 happen before n2)
      seq_edges :: [(CSNode, CSNode)]
      seq_edges = [ (r2, r1) | (r1, r2s) <- seq_graph, r2 <- r2s ]
                  ++ rb_edges

      -- separate the outgoing edges from methods
      (meth_outgoing_edges, seq_edges_minus_meth_outgoing) =
          partition (isMethodId . getCSNId . fst) seq_edges

      -- make the outgoing edges easily searchable
      meth_outgoing_edges_map :: M.Map AId [CSNode]
      meth_outgoing_edges_map =
          let
              -- Note that we start with all nodes from "meth_outgoing_edges",
              -- not just Exec nodes.  This is to address bug 1345, where
              -- conditional execution of a method inside a parent rule means
              -- that the scheduling of the method is decided inside the
              -- execution of the rule.  So we include paths from the Sched
              -- node as well. In case this breaks existing designs,
              -- a flag can be used to revert to the old behavior.
              edges = if (strictMethodSched flags)
                      then meth_outgoing_edges
                      else filter (isCSNExec . fst) meth_outgoing_edges

              -- remove edges going into methods
              filtered_edges :: [(CSNode, CSNode)]
              filtered_edges =
                  filter (not . isMethodId . getCSNId . snd) edges

              -- change the index to just the method Id and join by Id
              lookup_pairs :: [(AId, [CSNode])]
              lookup_pairs = joinByFst $ mapFst getCSNId filtered_edges
          in  M.fromList lookup_pairs

      -- Convert the remaining edges to a Graph from GraphWrapper,
      -- and use that to find the reachable nodes
      -- which will allow us to compute the reachable nodes
      -- seq_reachables: reachable points from all nodes
      seq_reachables :: [(CSNode, [(CSNode, [CSNode])])]
      seq_reachables = unsafePerformIO $ do
        seq_path_graph <- GW.makeGraph seq_nodes seq_edges_minus_meth_outgoing
        reachables <- GW.findReachablesIO seq_path_graph seq_nodes
        return (zip seq_nodes reachables)

      -- keep just the reachable method Ids (with their paths)
      -- and make a map for easy lookup
      -- (Notice that the associated list has not had "nub" applied;
      -- if there are paths to both sched and exec, the first one in the
      -- list will be found and used.  This is ok, because a path to the
      -- sched node will lead to the exec node.)
      reachable_meth_map :: M.Map CSNode [(AId, [CSNode])]
      reachable_meth_map =
          let -- only keep the reachable method Ids
              prune_reachables (n, rs) =
                  let -- convert the reachable node to Id,
                      rs_by_id = mapFst getCSNId rs
                      -- keep only the methods
                      rs_filtered = filter (isMethodId . fst) rs_by_id
                  in  (n, rs_filtered)
              reachable_meths = map prune_reachables seq_reachables
              -- filtering out empty lists should filter out reachables
              -- from method nodes, as well as not storing empty lists in
              -- the map
              filtered_reachables = filter (not . null . snd) reachable_meths
          in  M.fromList filtered_reachables

  in (reachable_meth_map, meth_outgoing_edges_map)

-- for rules/methods which calls submodule method pairs that have a rule
-- between them, create a new node for that rule and edges in and out,
-- to be used in the reachability graph to compute rule-between-methods
-- for methods of the current module
--
-- XXX This duplicates work done in "verifyStaticScheduleTwoRules".
-- XXX Perhaps we should have computed this info once, and passed it to
-- XXX both locations?
makeRuleBetweenEdges :: RuleBetweenMap -> RuleMethodUseMap -> [ARuleId] -> SchedOrdMap ->
                        ([CSNode], [(CSNode, CSNode)])
makeRuleBetweenEdges ruleBetweenMap ruleMethodUseMap ruleNames sched_id_order =
    let
        -- when we create new nodes, we want to qualify the subrule by
        -- its instance
        qualifyRuleId inst rule = addToBase inst rule

        -- avoid computing the same pair twice by folding over the list
        checkOneRule :: [(ARuleId, (AExpr, M.Map AId [(AId, AExpr)]))] ->
                        [(CSNode, [(CSNode, CSNode)])]
        checkOneRule ((r1, (_, r1_usemap)):rest) =
          let
              r2s = map fst rest

              checkSecondRule :: ARuleId -> Maybe (CSNode, [(CSNode, CSNode)])
              checkSecondRule r2 | (r1 == r2) = Nothing
              checkSecondRule r2 =
                let
                    r2_usemap =
                        case (M.lookup r2 ruleMethodUseMap) of
                            Just (_, res) -> res
                            Nothing -> internalError
                                         ("makeRuleBetweenEdges: " ++
                                          "r2_usemap: " ++ getIdString r2)

                    checkOneInstance ::
                        (AId, [(AId, AExpr)]) ->
                        -- Left indicates (r1,r2), Right indicates (r2,r1)
                        Maybe (Either ARuleId ARuleId)
                    checkOneInstance (inst, methods1) =
                        let
                            -- to minimize the creation of new node,
                            -- we just return the first rule
                            lookupRule m1 m2 =
                              case (M.lookup (m1,m2) ruleBetweenMap) of
                                Just (r:_) -> Just (Left r)
                                Nothing ->
                                  case (M.lookup (m2,m1) ruleBetweenMap) of
                                    Just (r:_) -> Just (Right r)
                                    Nothing -> Nothing
                                    Just [] ->
                                        internalError ("lookupRule: " ++
                                                       "no rules: " ++
                                                       ppReadable (m2,m1))
                                Just [] -> internalError ("lookupRule: " ++
                                                          "no rules: " ++
                                                          ppReadable (m1,m2))
                            pairs =
                              [ (m1, m2)
                                  | let m_methods2 = M.lookup inst r2_usemap,
                                    (Just methods2) <- [m_methods2],
                                    (methId1, _) <- methods1,
                                    (methId2, _) <- methods2,
                                    methId1 /= methId2,
                                    let m1 = MethodId inst methId1,
                                    let m2 = MethodId inst methId2
                              ]
                            rules_between_one_instance =
                                -- we've already checked for rules-between
                                -- in opposite directions, so these will
                                -- either be Left or Right (if any at all)
                                mapMaybe (uncurry lookupRule) pairs
                        in
                            case rules_between_one_instance of
                                ((Left r):_) ->
                                    let r_qual = qualifyRuleId inst r
                                    in  Just (Left r_qual)
                                ((Right r):_) ->
                                    let r_qual = qualifyRuleId inst r
                                    in  Just (Right r_qual)
                                [] -> Nothing

                    rules_between_one_rule =
                        mapMaybe checkOneInstance (M.toList r1_usemap)
                in case rules_between_one_rule of
                        ((Left r):_) ->
                            let node = mkCSNExec_tmp r
                                -- r1 before r before r2
                                edges = [(mkCSNExec sched_id_order r1, node),
                                         (node, mkCSNExec sched_id_order r2)]
                            in  Just (node, edges)
                        ((Right r):_) ->
                            let node = mkCSNExec_tmp r
                                -- r2 before r before r1
                                edges = [(mkCSNExec sched_id_order r2, node),
                                         (node, mkCSNExec sched_id_order r1)]
                            in  Just (node, edges)
                        [] -> Nothing

              r1_result = mapMaybe checkSecondRule r2s
          in
              r1_result ++ checkOneRule rest
        checkOneRule [] = []

        (new_nodes_dups, new_edgess) =
            unzip $ checkOneRule (M.toList ruleMethodUseMap)
        new_edges = concat new_edgess
        new_nodes = fastNub new_nodes_dups
    in (new_nodes, new_edges)


findRuleBetweenMethods :: [ARuleId] ->
                          M.Map AId [CSNode] ->
                          M.Map CSNode [(AId, [CSNode])] ->
                          [((ARuleId,ARuleId), [ARuleId])]
findRuleBetweenMethods ifcRuleNames
                       meth_outgoing_edges_map reachable_meth_map =
  let
      findReachableMeths n = fromMaybe [] (M.lookup n reachable_meth_map)

      findOutgoingEdges m =
          -- if it's not in the map, there are no outgoing edges
          fromMaybe [] (M.lookup m meth_outgoing_edges_map)

      -- A function which tells whether m1 SB m2 due to a rule being
      -- executable only between the two.  (By applying m1 first, and
      -- then using on multiple m2, we can avoid multiple lookups.)
      hasRuleBetween :: ARuleId -> ARuleId -> Maybe [ARuleId]
      hasRuleBetween m1 m2 | m1 == m2 = Nothing
      hasRuleBetween m1 m2 =
        let
            out_rs = findOutgoingEdges m1
            reachable_methods =
                M.fromList $ concatMap findReachableMeths out_rs
        in
            case (M.lookup m2 reachable_methods) of
               Nothing -> Nothing
               Just raw_path ->
                  let -- the path is in reverse and the head of the list
                      -- should be method m2; drop the head to leave just
                      -- the rule path and reverse to put in proper order
                      path_nodes =
                          if (length raw_path > 1)
                          then reverse (tail raw_path)
                          else internalError
                                   ("ASchedule hasRuleBetween: " ++
                                    "path too short: " ++
                                    ppReadable raw_path ++
                                    "  m1=" ++ ppReadable m1 ++
                                    "  m2=" ++ ppReadable m2)
                      -- get the Ids and remove duplicates
                      -- (in case the sched and exec are both in the list)
                      path_ids = nub (map getCSNId path_nodes)
                  in
                      Just path_ids

      hasRulePairs :: [((ARuleId,ARuleId), [ARuleId])]
      hasRulePairs =
          [ ((m1,m2), path)
              | m1 <- ifcRuleNames,
                m2 <- ifcRuleNames,
                m1 /= m2,
                let mpath = hasRuleBetween m1 m2,
                isJust mpath,
                let path = fromJustOrErr "hasRulePairs" mpath
          ]
  in
      hasRulePairs


findRuleBeforeMethods :: [ARuleId] -> [ARuleId] ->
                         M.Map AId VSchedInfo -> M.Map AId [MethodId] ->
                         M.Map CSNode [(AId, [CSNode])] ->
                         [(ARuleId, [Either ARuleId AMethodId])]
findRuleBeforeMethods ifcRuleNames userRuleNames
                      sub_schedinfo_map method_meth_map reachable_meth_map =
  let
      -- pair methods with the rules which must precede them
      rule_method_pairs = [ (m,[Left r])
                          | (n1,reachables) <- M.toList reachable_meth_map
                          , let r = getCSNId n1
                          , r `elem` userRuleNames
                          , (m,_)  <- reachables
                          ]

      -- also look for methods used which have a rule before them
      inherit_before (MethodId i m) =
          case M.lookup i sub_schedinfo_map of
            Nothing -> internalError ("findRuleBeforeMethods: no instance " ++
                                      show i)
            (Just si) -> case (lookup m (rulesBeforeMethods si)) of
                           Nothing  -> Nothing
                           (Just _) -> Just (Right m)
      meth_method_pairs = [ (r, xs)
                          | r <- ifcRuleNames
                          , let ms = M.findWithDefault [] r method_meth_map
                          , let xs = mapMaybe inherit_before ms
                          , not (null xs)
                          ]

      before = map_insertManyWith (++)
                   (rule_method_pairs ++ meth_method_pairs)
                   M.empty
      hasRuleBefore :: [(AId,[Either ARuleId AMethodId])]
      hasRuleBefore = [ (m,nub xs) | (m,xs) <- M.toList before ]
  in
      hasRuleBefore

-- --------------------

findUnsyncMethods :: [ARuleId] -> M.Map AId VSchedInfo ->
                     M.Map AId [MethodId] -> [ARuleId]
findUnsyncMethods ifcRuleNames sub_schedinfo_map method_meth_map =
  let is_unsync (MethodId i m) =
          case M.lookup i sub_schedinfo_map of
            Nothing -> internalError ("findUnsyncMethods: no instance " ++
                                      show i)
            (Just si) -> m `elem` (clockCrossingMethods si)
  in [ r
     | r <- ifcRuleNames
     , any is_unsync (M.findWithDefault [] r method_meth_map)
     ]

-- --------------------

-- add CF annotations for ready methods
-- they are CF with all other methods (ready or not)
-- because the real scheduling is done with the "main" method
-- not otherwise generated because we filter them out in cvtIfc
addReadyCF :: [PProp] -> [ARuleId] -> VSchedInfo -> VSchedInfo
addReadyCF pps meths vsi = vsi { methodConflictInfo = mci' }
  where mci = methodConflictInfo vsi
        mci' = mci { sCF = sCF mci ++ readyPairs }
        -- do not introduce annotations for ready signals of
        -- always_ready methods - the corresponding interface
        -- methods won't exist
        meths_noAR = filter (not . (isAlwaysRdy pps)) meths
        (readys, nonReadys) = partition isRdyId meths_noAR
        -- avoid nub by being careful with the generation
        readyPairs = uniquePairs readys ++
                     selfPairs readys ++
                     [ (x,y) | x <- readys, y <- nonReadys ]

-- fixSchedInfo: fix scheduling annotations for rules that have
--               been generated through splits (on if expressions)
fixSchedInfo :: [(ARuleId, [ARuleId])] -> VSchedInfo -> VSchedInfo
fixSchedInfo [] vsi = vsi
fixSchedInfo name_pairs (SchedInfo mci rms rbm ccm) =
    -- the fixing of the MethodConflictInfo is done in an accumulating way
    -- while the fixing of the rule-between info can be done simpler,
    -- so we split them apart
    let mci'     = fixMethodConflictInfo name_pairs mci
        name_map = M.fromList [ (r, orig)
                              | (orig, rs) <- name_pairs
                              , r <- rs, not (orig == r)
                              ]
        rms' = fixRuleBetweenInfo name_map rms
        rbm' = fixRuleBeforeInfo name_map rbm
        ccm' = fixUnsyncMethodInfo name_map ccm
    in (SchedInfo mci' rms' rbm' ccm')

fixRuleBetweenInfo :: M.Map ARuleId ARuleId ->
                      [((ARuleId, ARuleId), [ARuleId])] ->
                      [((ARuleId, ARuleId), [ARuleId])]
fixRuleBetweenInfo name_map rms =
    -- don't do work if there's been no splitting
    if (M.null name_map)
    then rms
    else fastNub [ ((m1', m2'), p)
                 | ((m1, m2), p) <- rms
                 , let m1' = M.findWithDefault m1 m1 name_map
                 , let m2' = M.findWithDefault m2 m2 name_map
                 ]

fixRuleBeforeInfo :: M.Map ARuleId ARuleId ->
                     [(ARuleId, [Either ARuleId AMethodId])] ->
                     [(ARuleId, [Either ARuleId AMethodId])]
fixRuleBeforeInfo name_map rbm =
    -- don't do work if there's been no splitting
    if (M.null name_map)
    then rbm
    else let fixName m = M.findWithDefault m m name_map
             fixEither (Right m) = Right (fixName m)
             fixEither x         = x
         in fastNub [ (fixName m, map fixEither p) | (m,p) <- rbm ]

fixUnsyncMethodInfo :: M.Map ARuleId ARuleId -> [ARuleId] -> [ARuleId]
fixUnsyncMethodInfo name_map ccm =
    -- don't do work if there's been no splitting
    if (M.null name_map)
    then ccm
    else fastNub [ M.findWithDefault m m name_map | m <- ccm ]

fixMethodConflictInfo :: [(ARuleId, [ARuleId])] ->
                         VMethodConflictInfo -> VMethodConflictInfo
fixMethodConflictInfo [] mci = mci
fixMethodConflictInfo ((rOrig, [rOrig']):rss) mci
   | rOrig == rOrig' = fixMethodConflictInfo rss mci
fixMethodConflictInfo ((rOrig, rs):rss) (MethodConflictInfo sCF sSB _ _ sSBR sC _) =
    fixMethodConflictInfo rss mci
    where
      -- rOrig = name of original rule
      -- rs = list of rules that correspond to original rule
      -- rss = the rest of the rules that are split
      -- mci = accumulating parameter

      -- check if one/both of r1 or r2 comes from rOrig
      eitherRS (r1,r2) = r1 `elem` rs || r2 `elem` rs
      bothRS (r1,r2) = r1 `elem` rs && r2 `elem` rs

      -- flipRS: given a list of pairs of rules, make sure that the first
      --         rule in each pair comes from rOrig (given that at least
      --         one of them do)
      flipRS = map (\(r1,r2) -> if r1 `elem` rs then (r1,r2) else (r2,r1))

      -- badXX: annotations for methods that come from rOrig
      -- sXX': annotations for all other rules
      (badCF, sCF') = partition eitherRS sCF
      (badSB, sSB') = partition eitherRS sSB
      (badSBR, sSBR') = partition eitherRS sSBR
      (badC, sC') = partition eitherRS sC

      -- badXX': remove annotations between different rules that all come
      --         from rOrig. That is, we always assume that a split method
      --         conflicts with itself.
      --
      --         In the case of badCF', badC' we also apply flipRS to make sure
      --         that the split method is on the left.
      --
      -- XXX There is room for two small optimizations:
      -- XXX  - If rOrig has no arguments, and all branches have the same
      -- XXX    annotation, then the whole method could inherit that annotation
      -- XXX  - If a branch is unreachable, that branch can be removed,
      -- XXX    possibly resulting in a simpler case

      badCF' = flipRS $ filter (not . bothRS) badCF
      badC' = flipRS $ filter (not . bothRS) badC
      badSB' = filter (not . bothRS) badSB
      badSBR' = filter (not . bothRS) badSBR

      -- leftSB: all SB annotations where the method coming from rOrig is on
      -- the left side (rightSB, leftSBR, and rightSBR are similar)
      (leftSB, rightSB) = partition (\(r1,r2) -> r1 `elem` rs) badSB'
      (leftSBR, rightSBR) = partition (\(r1,r2) -> r1 `elem` rs) badSBR'

      -- Add all CF annotations to list of SB (and all CF and SB to list of SBR)
      -- That is, add all annotations that are more permissive.
      leftSB' = leftSB ++ badCF'
      leftSBR' = leftSBR ++ leftSB'
      rightSB' = map flipTpl rightSB ++ badCF'
      rightSBR' = map flipTpl rightSBR ++ rightSB'

      -- newCF: all CF annotations related to rOrig
      cfrs = isCFWithAll badCF'
      newCF = [(rOrig,r') | r' <- cfrs]

      -- newC: all C annotations related to rOrig
      -- we assume a split method conflict with itself, above
      -- so record that
      confrs = isCWithAny badC'
      newC_1 = (rOrig, rOrig):[(rOrig,r') | r' <- confrs]

      -- notCF: given a list of rules, remove the ones that are known to
      --        be CF with the rOrig
      notCF :: [ARuleId] -> [ARuleId]
      notCF = filter (not . (`elem` cfrs))

      -- sbs: all SB annotations related to rOrig
      leftSBNew = notCF $ isCFWithAll leftSB'
      rightSBNew = notCF $ isCFWithAll rightSB'
      newSB = [(rOrig,r') | r' <- leftSBNew] ++
              [(r',rOrig) | r' <- rightSBNew]

      notCFOrSB = filter (not .(`elem` (leftSBNew ++ rightSBNew))) . notCF

      -- sbrs: all SBR annotations related to rOrig
      leftSBRNew = notCFOrSB $ isCFWithAll leftSBR'
      rightSBRNew = notCFOrSB $ isCFWithAll rightSBR'
      newSBR = [(rOrig,r') | r' <- leftSBRNew] ++
               [(r',rOrig) | r' <- rightSBRNew]

      notCFOrSBOrSBR = filter (not .(`elem` (leftSBRNew ++ rightSBRNew))) . notCFOrSB

      -- some methods conflict because different branches
      -- go in different directions - accumulate them here
      -- use leftSBR' and rightSBR' because thet are the most complete sets
      -- the only check required is that the method
      -- isn't in any previous set
      leftAndRightC = nub $ ((notCFOrSBOrSBR $ (map snd) leftSBR') ++
                             (notCFOrSBOrSBR $ (map snd) rightSBR'))

      newC_2 = [(rOrig, r') | r' <- leftAndRightC ]
      newC = nub (newC_1 ++ newC_2)

      -- Update the accumulating parameter:
      mci = MethodConflictInfo {
                 sCF = newCF ++ sCF',
                 sSB = newSB ++ sSB',
                 sME = [],
                 sP = [],
                 sSBR = newSBR ++ sSBR',
                 sC = newC ++ sC',
                 sEXT = []
             }


      -- isCFWithAll: given a list of pairs of rules, where the left rule comes
      --              from rOrig, return all rules occurring to the right, such
      --              that it occurs at least once together with every rule in rs
      --              (that is together with every rule coming from rOrig)
      --
      --   Works by turning the list [(a,1),(a,2),(b,3)] into [(a,[1,2]),(b,[3])],
      --   (and then add (c,[]) if there is such a c), and finally returning the
      --   intersection of all the lists to the right in the tuples
      isCFWithAll :: [(ARuleId, ARuleId)] -> [ARuleId]
      isCFWithAll = intersectAll . map snd . G.toVAList . addMissing .
                    foldl G.addEdge G.empty . map (\(a,b) -> (a,b,()))

      intersectAll [] = []
      intersectAll xs = foldl1 intersect xs

      -- isCWithAny : give a list of pairs of rules, where the left rule
      --              comes from rOrig, return all rules occurring on the right
      --              without duplicates (since if any branch conflicts with you
      --              the method as a whole conflicts
      isCWithAny :: [(ARuleId, ARuleId)] -> [ARuleId]
      isCWithAny = nub . (map snd)

      -- add subrules that don't have any conflicts
      addMissing g = foldl G.addVertex g
                   (filter (not . (`elem` (map fst $ G.toList g))) rs)

      flipTpl (a,b) = (b,a)


-- ========================================================================
-- Verify rule assertions
--

verifyAssertion :: ASchedule -> (M.Map CSNode [CSNode]) ->
                   RuleBeforeMap -> (S.Set MethodId) ->
                   (M.Map ARuleId [MethodId]) -> SchedOrdMap ->
                   (ARuleId,RulePragma) -> SM ()
verifyAssertion sch@(ASchedule ss _) pred_map before_map unsync_set meth_map sched_id_order a@(rid, rpragma) =
    do let check_fire_when_enabled = (rpragma == RPfireWhenEnabled) ||
                                     (rpragma == RPclockCrossingRule)
           check_no_rules_before = (rpragma == RPcanScheduleFirst) ||
                                   (rpragma == RPclockCrossingRule)
           check_no_unsync_methods = (rpragma == RPclockCrossingRule)
           fwe_msgs = if check_fire_when_enabled
                      then mapMaybe (verifyAssertionSr a) ss
                      else []
           before_sched = M.findWithDefault [] (mkCSNSched sched_id_order rid) pred_map
           before_exec  = M.findWithDefault [] (mkCSNExec  sched_id_order rid) pred_map
           nrb_msgs = if (check_no_rules_before &&
                          (not ((null before_sched) && (null before_exec))))
                      then [errCannotScheduleFirst a before_sched before_exec]
                      else []
           meths = M.findWithDefault [] rid meth_map
           befores = [ (m,rs)
                     | m <- meths
                     , let rs = M.findWithDefault [] m before_map
                     , not (null rs)
                     ]
           nrb2_msgs = if ((check_no_rules_before) && (not (null befores)))
                       then [errCannotScheduleFirstViaMeth a befores]
                       else []
           unsynced = filter (`S.member` unsync_set) meths
           unsync_msgs = if ((check_no_unsync_methods) && (not (null unsynced)))
                       then [errCascadedDomainCrossing a unsynced]
                       else []
           emsgs = fwe_msgs ++ nrb_msgs ++ nrb2_msgs ++ unsync_msgs
       when (not (null emsgs)) $
              throwError (EMsgs emsgs)

-- Given an assertion and a scheduler group, returns Maybe EMsg
verifyAssertionSr :: (ARuleId, RulePragma) -> AScheduler -> Maybe EMsg
verifyAssertionSr a@(r,rpragma) sch@(ASchedEsposito fs)
  | (rpragma == RPfireWhenEnabled) || (rpragma == RPclockCrossingRule) =
    case (lookup r fs) of
        Nothing -> Nothing
        Just [] -> Nothing
        Just conflicts ->
                   Just (errFireWhenEnabledBecauseBlocked a conflicts sch)
verifyAssertionSr (_, rpragma) _ =
    internalError ("ASchedule.verifyAssertionSr " ++ show rpragma)


-- --------------------

assertErrorMessage :: (ARuleId, RulePragma) -> Maybe Doc -> EMsg
assertErrorMessage (r,a) mreason =
    (getIdPosition r,
     ERuleAssertion (pfpString r) (getRulePragmaName a) mreason)

errFireWhenEnabledBecauseBlocked :: (ARuleId, RulePragma) -> [ARuleId]
                                 -> AScheduler -> EMsg
errFireWhenEnabledBecauseBlocked a rs sch =
    errFireWhenEnabledBecause a rs sch
        "because it is blocked by rule"

errFireWhenEnabledBecause :: (ARuleId, RulePragma) -> [ARuleId]
                          -> AScheduler -> String -> EMsg
errFireWhenEnabledBecause a rs sch because_string =
    let s = case rs of { [_] -> ""; _ -> "s" }
        reason = s2par (because_string ++ s) $$
                 nest 2 (foldr1 ($$) (map (pfPrint PDReadable 0) rs)) $$
                 s2par ("in the scheduler") $$
                 -- there is no PVPrint instance for ASchedule
                 nest 2 (pPrint PDReadable 0 sch)
    in  assertErrorMessage a (Just reason)

errCannotScheduleFirst :: (ARuleId, RulePragma) -> [CSNode] -> [CSNode]
                       -> EMsg
errCannotScheduleFirst a before_sched before_exec =
    let s_msg = describe "scheduled" before_sched
        e_msg = describe "executed" before_exec
        reason = case (before_sched,before_exec) of
                   ([],[])   -> internalError "errCannotScheduleFirst"
                   ([],_)    -> e_msg "because"
                   (_,[])    -> s_msg "because"
                   otherwise -> (s_msg "because") $$ (e_msg "and")
    in assertErrorMessage a (Just reason)
  where describe before nodes prefix =
          let hdr = text (prefix ++ " before it can be " ++ before ++ ":")
              lst = [ rule <+> (text "must be") <+> action
                    | n <- nodes
                    , let rule = pPrint PDReadable 0 (getCSNId n)
                    , let action = if (isCSNSched n)
                                   then text "scheduled"
                                   else text "executed"
                    ]
          in hdr $+$ (nest 2 (vsep lst))

errCannotScheduleFirstViaMeth :: (ARuleId, RulePragma)
                              -> [(MethodId, [Either ARuleId AMethodId])]
                              -> EMsg
errCannotScheduleFirstViaMeth a befores =
    let hdr = text ("because it uses methods which require rules to execute before it:")
        lst = map describe befores
        reason = hdr $+$ (nest 2 (vsep lst))
    in assertErrorMessage a (Just reason)
  where describe (m,rs) =
          let mname = pPrint PDReadable 0 m
              rnames = [ pPrint PDReadable 0 r | (Left r) <- rs ]
              vmnames = [ pPrint PDReadable 0 vm | (Right vm) <- rs ]
              rdoc = (text "schedules after the rule(s):") <+> (hsep rnames)
              mdoc = (text "schedules after rules via the method call(s):") <+> (hsep vmnames)
          in case (rnames,vmnames) of
               ([],[]) -> internalError "errCannotScheduleFirstViaMeth: no rules or methods"
               (_,[])  -> mname <+> rdoc
               ([],_)  -> mname <+> mdoc
               (_,_)   -> mname <+> rdoc <+> (text "and") <+> mdoc

errCascadedDomainCrossing :: (ARuleId, RulePragma) -> [MethodId] -> EMsg
errCascadedDomainCrossing a unsynced =
    let hdr = text ("because it uses methods which are themselves unsychronized domain crossings:")
        lst = map describe unsynced
        reason = hdr $+$ (nest 2 (vsep lst))
    in assertErrorMessage a (Just reason)
  where describe m = pPrint PDReadable 0 m

-- ========================================================================
-- Database of rule exclusivity (for proper muxing in later stages)
--

-- create a map indexed by two rules with per-pair conflict information values
-- XXX this probably still computes disjointness for too many rules
-- unless other uses are required we should only compute disjointness for
-- rules that call methods with argumnets
mkExclusiveRulesDB :: [Id] -- all rule identifiers
                   -> RuleUsesMap -- used to test if two rules have any method calls in common
                   -> RuleDisjointTest -- function to test rule disjointness (for rules with methods in common)
                   -> RuleDisjointTest -- function to test if rules have been annotated conflict-free
                   -> ConflictMap -- CF conflict map
                   -> ConflictMap -- SC conflict map
                   -> [(Id,Id,[Conflicts])] -- conflicts from resource allocation
                   -> [(Id,Id,[Conflicts])] -- conflicts from cycle dropping
                   -> [(Id,Id,[Conflicts])] -- conflicts from earliness priorities
                   -> ExclusiveRulesDB
mkExclusiveRulesDB rule_names rule_uses_map are_disjoint are_cf cf_map sc_map
                   res_drops cycle_drops earliness_drops =
  let
      rule_objs_map = rumToObjectMap rule_uses_map
      getRuleObjUses r =
          fromJustOrErr ("mkExclusiveRulesDB: getRuleObjUses: " ++ ppReadable r)
              (M.lookup r rule_objs_map)

{-
      -- for efficiency, this was moved into mkOneRule
      share_uses r1 r2 = not (S.null (r1_uses `S.intersection` r2_uses))
        where r1_uses = getRuleObjUses r1
              r2_uses = getRuleObjUses r2

      r1 `disjoint` r2 = share_uses r1 r2 && are_disjoint r1 r2
-}

      r1 `excludes` r2 = -- are r1 and r2 exclusive?
            let match_rule_names (r1',r2',_) = r1 == r1' && r2 == r2'
                -- XXX lookup in sc_map only means that r1 affects something
                -- XXX that r2 reads, not they are exclusive!
                conflicts_sc = (r1,r2) `G.member` sc_map
                conflicts_res = any match_rule_names res_drops
                conflicts_cycle = any match_rule_names cycle_drops
                conflicts_prio = any match_rule_names earliness_drops
                -- we would need to do method-level analysis to figure out which
                -- method calls can be marked exclusive for CF-annotated rules
                -- method calls that are SBR are not exclusive (they just say "last caller wins")
                -- and so they need primuxes even if the rules are marked CF
                -- only method calls that are C can be treated as exclusive
                -- (i.e. build the parallel mux because if the selects aren't exclusive the results are nonsense anyway)
                -- forced_cf = are_cf r1 r2
            in
                -- we assume that the caller has already checked that:
                -- not (r1 `disjoint` r2)
                conflicts_sc || conflicts_res ||
                conflicts_cycle || conflicts_prio

      -- Note: to conserve memory, the second set of information excludes
      -- values which also appear in the first set.  That is, the second
      -- set records rules which are exclusive but not disjoint, and the
      -- full set of exclusive rules is the union of the two sets.
      mkOneRule r1 =
          let
              -- define this here, so that we don't keep looking up r1
              -- XXX does this actually help? or is GHC smart enough to opt this?
              r1_uses = getRuleObjUses r1
              shares_uses r2 =
                  let r2_uses = getRuleObjUses r2
                  in  not (S.null (r1_uses `S.intersection` r2_uses))
              r1 `disjoint` r2 = shares_uses r2 && are_disjoint r1 r2

              foldFunc (accum_ds, accum_es) r2
                  | (r1 `disjoint` r2) = (S.insert r2 accum_ds, accum_es)
                  | (r1 `excludes` r2) = (accum_ds, S.insert r2 accum_es)
                  | otherwise          = (accum_ds, accum_es)
              (ds, es) = foldl foldFunc (S.empty, S.empty) rule_names
          in
              if (S.null ds && S.null es)
              then []
              else [(r1, (ds, es))]

      rs = concatMap mkOneRule rule_names
  in
      ExclusiveRulesDB (M.fromList rs)


-- ========================================================================
-- User-requested rule relationship queries
--

mkRuleRelationDB :: [ARuleId] -> (ARuleId -> ARuleId -> Bool) ->
                    ConflictMap -> ConflictMap ->
                    [(ARuleId, ARuleId, [Conflicts])] ->
                    [(ARuleId, ARuleId, [Conflicts])] ->
                    [(ARuleId, ARuleId, [Conflicts])] ->
                    [(CSNode, CSNode, CSEdge)] ->
                    RuleRelationDB
mkRuleRelationDB rule_names rule_disjoint cf_map sc_map
                 res_drops cycle_drops sched_pragma_drops arb_edges =
  let
      arb_map :: M.Map (ARuleId, ARuleId) Conflicts
      arb_map =
          let convEdgeConflict (CSE_Conflict [c]) = c
              convEdgeConflict (CSE_Conflict cs) =
                  internalError("mkRuleRelationDB: expected one CS edge: " ++
                                ppReadable cs)
              convEdgeConflict cse =
                  internalError("mkRuleRelationDB: expected CS conflict edge: "
                                ++ ppReadable cse)
              convEdge (csn1, csn2, cse) =
                  ((getCSNId csn1, getCSNId csn2), convEdgeConflict cse)
          in  M.fromList (map convEdge arb_edges)

      getPairInfo rule1 rule2 =
          let
              -- extract a conflict from a (r, r', conf) list
              -- (assume that each edge is a list of one conflict)
              get_conflict db =
                  let match_rule_names (r1',r2',_) =
                          rule1 == r1' && rule2 == r2'
                      extractOne [c] = c
                      extractOne cs =
                          internalError ("mkRuleRelationDB: " ++
                                         "expected one edge: " ++
                                         ppReadable (rule1, rule2, cs))
                  in  fmap (extractOne . thd) (find match_rule_names db)

              info = RuleRelationInfo {
                       mCF = lookupUseConflict (rule1,rule2) cf_map
                     , mSC = lookupUseConflict (rule1,rule2) sc_map
                     , mRes = get_conflict res_drops
                     , mCycle = get_conflict cycle_drops
                     , mPragma = get_conflict sched_pragma_drops
                     , mArb = M.lookup (rule1, rule2) arb_map
                     }
              minfo = if (info /= defaultRuleRelationship)
                      then (Just info)
                      else Nothing
          in ((rule1,rule2), rule1 `rule_disjoint` rule2, minfo)

      infos = [ getPairInfo r1 r2 | r1 <- rule_names, r2 <- rule_names ]

  in rrdbFromList infos

doQueries :: ErrorHandle -> Flags -> [ARuleId] -> RuleRelationDB -> IO ()
doQueries errh flags rule_names relationDB =
    mapM_ print_sched_infos (schedQueries flags)
    where -- print info for a pair of rules
          print_sched_info (rule1, rule2) =
              let (disj,rri) = getRuleRelation relationDB rule1 rule2
                  doc = printRuleRelationInfo rule1 rule2 disj rri
              in  putStrLn (ppDoc doc)
          -- print info for multiple rules specified in one query flag
          print_sched_infos (rules1, rules2) =
              case (find_rule_ids_from_strings rules1,
                    find_rule_ids_from_strings rules2) of
                  ([],[]) -> bsWarning errh [(cmdPosition, WMissingRule rules1),
                                             (cmdPosition, WMissingRule rules2)]
                  ([],_)  -> bsWarning errh [(cmdPosition, WMissingRule rules1)]
                  (_,[])  -> bsWarning errh [(cmdPosition, WMissingRule rules2)]
                  (r1s,r2s) -> mapM_ print_sched_info
                                     [ (r1,r2)
                                     | r1 <- r1s, r2 <- r2s, r1 /= r2
                                     ]
          find_rule_ids_from_strings "*" = rule_names
          find_rule_ids_from_strings rs =
              maybeToList $ find ((== rs) . getIdString) rule_names


-- ========================================================================
-- Conflict graph routines
--

-- Build a conflict graph for CF, PC, or SC

-- Conflict test
--   Given a set of the CF/PC/SC pairs from the SchedInfo of all
--   submodule instances, a conflict test is produced between rules
--   to determine whether the rules are CF/PC/SC.

--   Note that this requires the SchedInfo of submodules to be
--   complete (if the relationship for a pair of methods is not
--   specified, it will be assumed to not be CF/PC/SC).

--   Note that this requires the SchedInfo to be unique for each pair
--   (SB/SBR indicates the ability to compose in that direction and
--   not the inability to compose in the other direction; "a SB b, b
--   SB a" would be taken by this function to mean composable in both
--   directions, thus the parser should ban two different
--   relationships for the same pair).

-- Inputs:
--   ncset = no conflict CF/PC/SC set
--           (all CF/PC/SC method pairs in submodule SchedInfo)
--   ignore_conflicts = func to query to see if we are checking conflicts
--      (For CF: rules are disjoint or annotated conflict-free,
--       For PC/SC: rules are already CF according to the CF map)
--   rmap = rule method use map (info on which methods are uses by each rule)

-- Output:
--   A graph with a node for every rule/method.  There will be an edge
--   between two nodes if the two rules are not disjoint (in the case of CF)
--   or already captured in the CF graph (in the case of PC/SC)
--   and if the two rules use a pair of methods that conflict (ruling out
--   CF/PC/SC).
--   A set of pairs of rules, where existence in the set means that
--   method calls between the rules were ignored because their conditions
--   were disjoint.  This is used to limit the set of pairs that need to
--   be tested later for static scheduling (if the ignored calls had a rule
--   between them that would require dynamic scheduling).

-- The type aliases resolve to these types:
--   NoConflictSet    :: Set (MethodId,MethodId)
--   RuleDisjointTest :: ARuleId -> ARuleId -> Bool
--   RuleUsesMap      :: M.Map RuleId RuleUses

mkConflictMap :: Flags -> DisjointTestState ->
                 RuleMethodUseMap -> NoConflictSet -> RuleDisjointTest ->
                 SM (ConflictMap, S.Set (ARuleId, ARuleId), DisjointTestState)
mkConflictMap flags dtstate rule_meth_map ncset ignore_conflicts =
    let
        checkOneUse :: AExpr -> AExpr ->
                       ([(MethodId, MethodId)], Bool, DisjointTestState) ->
                       ((MethodId, AExpr), (MethodId, AExpr)) ->
                       SM ([(MethodId, MethodId)], Bool, DisjointTestState)
        checkOneUse p1 p2 (cs, b, dts) ((m1,c1), (m2,c2)) = do
          (res, dts') <- convIO $ checkDisjointExprWithCtx dts p1 p2 c1 c2
          case res of
            Just True -> return (cs, True, dts')
            _ -> let cs' = ((m1,m2):cs)
                           in  return (cs', b, dts')

        checkUses ::
          (ARuleId, (AExpr, MethodIdMap)) ->
          ([(ARuleId, [Conflicts])], S.Set (ARuleId, ARuleId), DisjointTestState) ->
          (ARuleId, (AExpr, MethodIdMap)) ->
          SM ([(ARuleId, [Conflicts])], S.Set (ARuleId, ARuleId), DisjointTestState)
        checkUses (rule1, (p1, usemap1)) (es, igns, dts) (rule2, (p2, usemap2)) =
          -- assume that checking disjointness is cheaper than computing
          -- the set of conflicts
          if (ignore_conflicts rule1 rule2)
          then return (es, igns, dts)
          else let cs = conflicts ncset usemap1 usemap2
               in if (null cs)
                  then return (es, igns, dts)
                  else if (not (schedConds flags))
                  then let cs' = map (\ ((m1,c1),(m2,c2)) -> (m1,m2)) cs
                           es' = ((rule2, [CUse cs']):es)
                       in  return (es', igns, dts)
                  else do (cs', ignored, dts')
                              <- foldM (checkOneUse p1 p2) ([], False, dts) cs
                          let igns' = if ignored
                                      then S.insert (rule1, rule2) igns
                                      else igns
                          if (null cs')
                            then return (es, igns', dts')
                            else let es' = ((rule2, [CUse (reverse cs')]):es)
                                 in  return (es', igns', dts')

        checkRule ::
          ([(ARuleId, [(ARuleId, [Conflicts])])], S.Set (ARuleId, ARuleId), DisjointTestState) ->
          (ARuleId, (AExpr, MethodIdMap)) ->
          SM ([(ARuleId, [(ARuleId, [Conflicts])])], S.Set (ARuleId, ARuleId), DisjointTestState)
        checkRule (ps, igns, dts) ru@(rule1, (p1, usemap1)) = do
          (es, igns', dts') <- foldM (checkUses ru) ([], igns, dts) (M.toList rule_meth_map)
          let ps' = ((rule1, es):ps)
          return (ps', igns', dts')
    in
        do (res, igns, dtstate') <-
               foldM checkRule ([], S.empty, dtstate) (M.toList rule_meth_map)
           return (G.fromList res, igns, dtstate')

-- ----------

type MethodIdMap = M.Map AId [(AId, AExpr)]

-- CONFLICTS of two uses wrt a no-conflict set
-- XXX Ugly hack to ignore ready signals.  Should this be dealt
-- XXX with elsewhere (AState.hs)?
conflicts :: NoConflictSet -> MethodIdMap ->  MethodIdMap ->
             [((MethodId, AExpr), (MethodId, AExpr))]
conflicts (NoConflictSet ncset) us1 us2 =
    -- traces ( "conflicts: " ++ ppReadable us ++ ppReadable us' ) $
    [ ((id1,c1), (id2,c2))
      | (obj, methset1) <- M.toList us1,
        (Just methset2) <- [M.lookup obj us2],
        (m1,c1) <- methset1, not (isRdyId m1),
        (m2,c2) <- methset2, not (isRdyId m2),
        let id1 = MethodId obj m1,
        let id2 = MethodId obj m2,
        not $ (id1,id2) `S.member` ncset ]


-- ----------

-- pick nodes to drop to make graph acyclic
drops :: [(ARuleId, [ARuleId])] -> [(ARuleId, ARuleId, [Conflicts])]
drops [] = []
drops graph@(_:_) = concat [thd (drops' mGraph (S.singleton root) [root] S.empty root) | (root:_) <- scc graph]
  where mGraph = M.fromList graph

-- Conceptually, takes a graph and a list of nodes reached so far and returns a pair
-- of a graph without cycles and a list of conflict edges used to
-- break the cycles. Note that the location at which a cycle is broken
-- depends on the choice of the root.
-- We use auxiliary sets and maps to make sure that this isn't wildly inefficient
-- The key turns out to be a skip set that makes sure we don't visit nodes
-- that we've already queued for processing
-- XXX This probably could be cleaned up with the right abstraction
-- possibly a SetList that keeps track of what has been added (and can give it back as an ordered list)
-- but uses a Set to test for membership - that's needed to give the right cycle error messages
-- We also should try to be clever about the skip handling
drops' :: M.Map ARuleId [ARuleId] -> S.Set ARuleId -> [ARuleId] ->
          S.Set ARuleId -> ARuleId ->
          (M.Map ARuleId [ARuleId],
           S.Set ARuleId,
           [(ARuleId, ARuleId, [Conflicts])])
drops' graph seen seenList skip root =
    case M.lookup root graph of
        Nothing -> errMissingRoot
        Just children ->
            let
                -- partition the nodes into those already visited,
                -- and those not yet visited
                (nasty, good) = partition (`S.member` seen) children
                -- to the output graph, add the edges which don't create cycles
                graph' = M.insert root good graph
                skip' = S.union skip (S.fromList good)
                -- skip nodes that we know will be visited
                good' = filter (`S.notMember` skip) good
                -- Takes a child node (which does not create a cycle),
                -- adds it to the list of visited nodes, and computes the
                -- acyclic graph and conflicts starting from that node.
                f (grph, skip, nsty) child =
                    let (grph', skip', nsty') = drops' grph (S.insert child seen) (child:seenList) skip child
                    in  (grph', skip', nsty++nsty')
            in
                -- Accumulate the graph and conflicts for all good children
                -- (don't create cycles), starting with a graph containing
                -- the good children and conflicts for the bad children.
              foldl f (graph',
                       skip',
                       [(child, root, [CCycle (child:seenList)])
                            | child <- nasty]) good'

errMissingRoot :: a
errMissingRoot = internalError "ASchedule: root missing from rule graph (!)"

warnCycleDrops :: AId -> [(ARuleId, ARuleId, [Conflicts])] -> ErrorMonad ()
warnCycleDrops moduleId cycleDrops =
    let
         warnDrop (child, root, cs) =
             let cycle = case (getCycleConflict cs) of
                           Just (CCycle rs) -> rs
                           _ -> internalError "warnCycleDrops"
             in  (getPosition moduleId,
                  WCycleDrop (to_string child) (to_string root)
                             (map to_string cycle))
    in  EMWarning (map warnDrop cycleDrops) ()


-- ========================================================================
-- Urgency graph routines
--

mkUrgencyMap :: [ARuleId] -> [(ARuleId, ARuleId, UrgencyEdge)] -> UrgencyMap
mkUrgencyMap vs es =
    let graph1 = foldl G.addVertex G.empty vs
    in  foldl G.addEdge graph1 es

flattenUrgencyMap :: Id -> UrgencyMap -> ErrorMonad [ARuleId]
flattenUrgencyMap moduleId umap =
    let
        -- vertices of the graph
        vs = G.vertices umap

        -- Convert umap to the format expected by tsort (topological sort).
        -- The pair (r1,r2) is added if there is a directed edge (r2,r1)
        -- in the umap.  This is because the output of tsort is in REVERSE
        -- order of the directed edges, and if we insert this way, rather
        -- than reverse the output of tsort, we get urgency order for
        -- unconstrained rules in the order in which they appeared in
        -- the code.
        ugraph = [(r, [r' | r' <- vs,
                            r' /= r,
                            -- let's try making the graph in the
                            -- opposite direction
                            -- (r,r') `G.member` umap])
                           (r',r) `G.member` umap])
                    | r <- vs]

    in
        -- tsort returns either an error or
        -- a list of rules and action methods in order of the directed edges
        either (errUrgencyCycles moduleId umap) return (tsort ugraph)


-- Given a strongly-connected component (SCC) reported by tsort,
-- report an error for the cycle.
-- We'd rather report a cycle to the user, than all edges in an SCC,
-- since a cycle is easier to understand; but we don't want to lose
-- information.  So, we report one cycle from the SCC and mention the
-- other rules which are also intertwined, in case that is helpful to
-- the user.
errUrgencyCycles :: AId -> UrgencyMap -> [[ARuleId]] -> ErrorMonad a
errUrgencyCycles moduleId umap sccs = EMError (map errUrgencyCycle sccs)
  where
    -- report an error for each SCC
    errUrgencyCycle :: [ARuleId] -> EMsg
    errUrgencyCycle scc =
        let path = GU.extractOneCycle_gmap umap scc
            -- the names of the nodes in the path
            path_strs = map pfpString path
            -- the names of the nodes not in the path, but in the SCC
            other_ids = scc \\ path
            other_strs = map pfpString other_ids
            -- the edges along the path
            path_edges = GU.findPathEdges umap path
            -- an explanation for each edge
            expl_doc = map (\(p,e) -> printUrgencyEdgePair p e) path_edges
        in
            (getPosition moduleId,
             EUrgencyCycle path_strs expl_doc other_strs)


-- ========================================================================
-- Convert ASyntax rules and interfaces to Rule
--

cvtARule :: ARule -> Rule
cvtARule (ARule rId _ _ _ rPred rActs _ rOrig) = Rule rId rOrig [rPred] [] rActs

-- convert a list of interface definitions into rules for computing
-- scheduling relationships
cvtIfc :: AIFace -> [Rule]
cvtIfc (AIAction _ _ ifPred ifId ifRs _) =
    [(Rule rId rOrig [ifPred, rPred] [ifPred, rPred] rActs)
        | (ARule rId rps rDesc rWireProps rPred rActs _ rOrig) <- ifRs]
cvtIfc (AIActionValue _ _ ifPred ifId ifRs (ADef dId t _ _) _) =
    -- similar to converting an action, but include the return value
    -- in the body value uses of each split rule
    -- (in this way, also, any value parts of an actionvalue method
    -- call will be in the same Rule structure as the action part)
    -- (note that, if the method body is not split into multiple
    -- rule, dId and rId will be the same)
    [(Rule rId rOrig [ifPred, rPred] [ifPred, rPred, dExpr] rActs)
        | (ARule rId rps rDesc rWireProps rPred rActs _ rOrig) <- ifRs]
        where dExpr = ASDef t dId
cvtIfc (AIDef _ _ _ ifPred (ADef dId t _ _) _ _)
    | isRdyId dId = []
    | otherwise   = [(Rule dId Nothing [ifPred] [ifPred,dExpr] [])]
        where dExpr = ASDef t dId
cvtIfc (AIClock {}) = []
cvtIfc (AIReset {}) = []
cvtIfc (AIInout {}) = []


-- ========================================================================
-- For each rule of the module, compute two things:
-- (1) all method uses
--     (for use in checking for dynamic scheduling between two rules)
-- (2) PC conflict information
--     (for use in checking for PC of all actions and in a rule, and
--      for checking for dynamic scheduling inside one rule)
--     (a) single method uses which are not PC with themselves
--     (b) pairs of different method uses (on the same state) which are not PC

-- ----------
-- data structures for the PC conflict map

-- the Ids are the method names (we don't need the full MethodId name,
-- because these are conflict pairs on one instance)
type PCConflictPairs = [((AId, [UniqueUse]), (AId, [UniqueUse]))]
-- for a rule, this is a map from instance Id to the pairs of conflicting
-- methods that the rule calls on that instance
type PCConflictPairsMap = M.Map AId PCConflictPairs

-- a map from a rule to:
-- (1) its predicate
-- (2) a list of all method uses which conflict with themselves
-- (3) a map of conflicting pairs called on each instance
type RulePCConflictUseMap = M.Map RuleId (AExpr, MethodUsesList, PCConflictPairsMap)

-- ----------
-- data structures for the map of all uses (sorted by instance)

-- a map from a rule to all method uses (sorted by instance)
-- Each method is paired with its call condition, for finer-grain scheduling.
-- The rule's predicate is included to save the effort of looking it up
-- when computing the full method call condition (the call condition AND'd
-- with the rule's predicate).
type RuleMethodUseMap = M.Map ARuleId (AExpr, M.Map AId [(AId, AExpr)])

-- ----------

makeRuleMethodUseMaps :: NoConflictSet -> RuleUsesMap ->
                         (RuleMethodUseMap,
                          RulePCConflictUseMap)
makeRuleMethodUseMaps (NoConflictSet setPC) ruleUseMap =
    let
        full_use_map :: M.Map ARuleId (AExpr, M.Map Id (M.Map Id [UniqueUse]))
        full_use_map = rumToMethodUseMap ruleUseMap

        -- Make a map from each rule to all the methods that rule calls,
        -- paired with the condition under which the method is called
        -- and organized by instance.  Also maintains the rule's predicate,
        -- to avoid the effort of looking it up.
        -- XXX this used to filter out ready signals; why?
        -- XXX it works fine without the filter now
        rule_meth_map = M.map convRuleUses full_use_map
          where
            convRuleUses (p, m) = (p, M.map (map convMethodUses . M.toList) m)

            convMethodUses :: (AId, [UniqueUse]) -> (AId, AExpr)
            convMethodUses (m, uus) = (m, aAnds (map extractCondition uus))

        -- convert the use-info into pc conflict info
        pc_conflict_map = M.map mkPCConflictInfo full_use_map

        mkPCConflictInfo :: (AExpr, M.Map Id (M.Map Id [UniqueUse])) ->
                            (AExpr, MethodUsesList, PCConflictPairsMap)
        mkPCConflictInfo (rp, usemap) =
          let
              -- a list of all methods (and their uses) which are called
              -- more than once and conflict with themselves
              singleMethodConfls :: MethodUsesList
              singleMethodConfls =
                  [ (m, uses)
                      | -- find all methods that are used at least twice
                        (objId, mus) <- M.toList usemap,
                        p@(methId, uses@(_:_:_)) <- M.toList mus,
                        let m = MethodId objId methId,
                        -- ... that are not PC with itself
                        not ((m,m) `S.member` setPC)
                  ]

              -- map from instance Id to a list of used method pairs
              -- which conflict
              pairMethodConfls :: PCConflictPairsMap
              pairMethodConfls =
                  let makePairConfls instId uses =
                          [ p |
                              -- find all pairs of used methods
                              -- (known to be on the same instance)
                              p@((methId1,uses1), (methId2,uses2))
                                  <- uniquePairs (M.toList uses),
                              -- that conflict with each other
                              let m1 = MethodId instId methId1,
                              let m2 = MethodId instId methId2,
                              not ((m1,m2) `S.member` setPC),
                              not ((m2,m1) `S.member` setPC)
                          ]
                  in  M.mapWithKey makePairConfls usemap
          in
              (rp, singleMethodConfls, pairMethodConfls)
    in
        (rule_meth_map, pc_conflict_map)


-- ========================================================================
-- Go through all rules of a module and check that all method calls in
-- each rule are pairwise PC (parallel composable)
--
-- We do this taking in a list of conflicting uses, which has already
-- been generated as follows:
--   * finding all method uses in the ruleUseMap
--   * for each rule, generate all pairs of method calls that affect
--     the same state
--   * discard the ones that are PC according to setPC
-- Then we further:
--   * discard the ones that are disjoint according to bddb
--
-- If any conflict remains, an error is reported

verifySafeRuleActions :: Flags -> [ADef] -> RulePCConflictUseMap ->
                         DisjointTestState -> SM DisjointTestState
verifySafeRuleActions flags userDefs rulePCConflictUseMap dtstate = do
      let
        --checkOneRule: returns all pairs of method uses (in a particular
        --              rule) that are not PC (according to setPC)
        checkOneRule ::
            (RuleId, (AExpr, MethodUsesList, PCConflictPairsMap))
            -> [(UniqueUse, UniqueUse, RuleId, AExpr)]
        checkOneRule (rule, (rp, allUses, usePairsMap)) =
          let -- conflicts: all pairs of conflicting method calls
              --            (of different methods)
              pairConflicts :: [(UniqueUse, UniqueUse, RuleId, AExpr)]
              pairConflicts =
                  [ (v1,v2,rule,rp) |
                      -- all pairs of used methods on the same state
                      (inst, usePairs) <- M.toList usePairsMap,
                      ((m1,uses1), (m2,uses2)) <- usePairs,
                      -- Extract the UniqueUses (for error message and
                      -- BDD analysis)
                      v1 <- uses1,
                      v2 <- uses2
                  ]

              -- singleRuleConfls: all pairs of conflicting calls to one method
              singleConflicts :: [(UniqueUse, UniqueUse, RuleId, AExpr)]
              singleConflicts =
                  [ (v1,v2,rule,rp) |
                      -- conflicting methods which are used
                      -- at least twice
                      (m, uses) <- allUses,
                      (v1,v2) <- uniquePairs uses
                  ]
          in pairConflicts ++ singleConflicts

        -- allConflicts: all calls that are conflicting, according to setPC
        allConflicts = concatMap checkOneRule (M.toList rulePCConflictUseMap)


      -- We will now discard the conflicts between rules that are disjoint

      -- Add a Bool to each pair of uses to indicate whether the uses are
      -- not disjoint.  (The Bool is False if the uses are disjoint)
      (disjoints, dtstate') <-
          convIO $ verifyDisjointActions dtstate allConflicts

      -- Filter out the disjoint uses, leaving only bad uses
      let useAction2 :: [(UniqueUse, UniqueUse, RuleId, AExpr, Bool)]
          useAction2 = filter (\ (_,_,_,_,res) -> res ) disjoints

      -- Prepare the error messages
      let show_all = showRangeConflict flags
          ppe = pPrintExpandFlags flags userDefs PDReadable bContext
          mkCondInfo c
              | isTrue c  = (False, Nothing)
              | show_all  = (False, Just $ ppe c)
              | otherwise = (True, Just $ text "...")
          mkArgs es
              | null es   = (False, empty)
              | show_all  = (False, commaSep (map ppe es))
              | otherwise = (True, text "...")
          -- (method, hasCond, args, moreInfo)
          getUseInfo :: UniqueUse -> (String, Maybe Doc, Doc, Bool)
          getUseInfo u@(UUExpr (AMethCall _ i m es) _) =
              let meth = getIdBaseString i ++ "." ++ getIdBaseString m
                  (moreCondInfo, cond) = mkCondInfo (extractCondition u)
                  (moreArgInfo, args) = mkArgs es
              in  (meth, cond, args, moreCondInfo || moreArgInfo)
          getUseInfo (UUExpr e _) =
              internalError ("getUseInfo: e = " ++ ppReadable e)
          getUseInfo (UUAction (ACall i m (c:es))) =
              let meth = getIdBaseString i ++ "." ++ getIdBaseString m
                  (moreCondInfo, cond) = mkCondInfo c
                  (moreArgInfo, args) = mkArgs es
              in  (meth, cond, args, moreCondInfo || moreArgInfo)
          getUseInfo (UUAction a) =
              internalError ("getUseInfo: a = " ++ ppReadable a)
          -- construct the error
          errGen bad@(u,u',r,_,_) =
            -- XXX include the rule predicate?
            (getIdPosition r, EParActionRangeConflict (pfpString r)
                                  (getUseInfo u) (getUseInfo u'))

          errorMessages = map errGen useAction2

      -- If the set of bad uses is not empty, report the errors
      if ( null errorMessages )
        then return dtstate'
        else throwError (EMsgs errorMessages)


-- Appends a boolean value indicating whether the uses overlap.
-- Returns False the if the uses are known (proven) to be disjoint --
-- that the uses do not intersect.  True otherwise, including the case
-- where it is unknown.
verifyDisjointActions :: DisjointTestState -> [(UniqueUse,UniqueUse,a,AExpr)] ->
                         IO ([(UniqueUse,UniqueUse,a,AExpr,Bool)], DisjointTestState)
verifyDisjointActions dtstate0 uses = do
    let checkOne (ress,dts) (u1,u2,r,rp) = do
          let (c1, c2) = (extractCondition u1, extractCondition u2)
          (res, dts') <- checkDisjointExprWithCtx dts rp rp c1 c2
          case res of
            -- if we're not sure, we assume that the
            -- uses overlap.
            Nothing -> return ((u1,u2,r,rp,True):ress, dts')
            -- if the actions are disjoint, then
            -- they cannot conflict
            Just b -> return ((u1,u2,r,rp,not b):ress, dts')
    --
    (results', dtstate1) <- foldM  checkOne ([], dtstate0) uses
    let results = reverse results'

    when (trace_disjoint_tests)
         (mapM_ (\ (u1,u2,r,rp,rs) ->
                 putStrLn $ "useDisjointTest: "
                  ++ ppReadable (extractCondition u1)
                  ++ " c2: " ++ ppReadable (extractCondition u2)
                  ++ " res: " ++ show rs
                 ) results )

    return (results, dtstate1)


-- ========================================================================
-- Checks that the design is not taking advantage of dynamic scheduling
-- due to separately synthesized schedulers, which would cause a problem
-- when trying to merge into one schedule (because a static execution order
-- could not be determined).

-- There are two checks:  One for exclusive method calls inside a single
-- rule (or method).  One for exclusive method calls between two rules
-- (or methods).  For both, we need a lookup of whether two methods have
-- a rule between them.

-- If a check fails, and the backend is Bluesim, we report an error.
-- If the backend is Verilog, we report a warning and taint any
-- generated .ba file as being for Verilog only.

-- ----------
-- RuleBetweenMap

type RuleBetweenMap = M.Map (MethodId, MethodId) [ARuleId]

-- make a lookup of whether a method pair has a rule (or rules) which
-- must execute between them in the given order (a lookup in the other
-- direction may be needed, for the other order)
makeRuleBetweenMap :: [AVInst] -> RuleBetweenMap
makeRuleBetweenMap avis =
    M.fromList $
    [ p | avi <- avis,
          let instId = avi_vname avi,
          let rbi = rulesBetweenMethods (vSched (avi_vmi avi)),
          ((methId1, methId2), rs) <- rbi,
          let m1 = MethodId instId methId1,
          let m2 = MethodId instId methId2,
          -- SchedInfo only stores the pair in the execution order
          -- (for one-rule lookup, either direction will do; but
          -- for two-rule lookup, we need to know the direction,
          -- so this map preserves it.
          let p = ((m1,m2),rs)
    ]

-- ----------
-- verifyStaticScheduleOneRule

-- Go through all rules of a module and check that all pairs of method
-- calls (on the same state) can be composed with a static schedule.

-- Note: We assume that it is safe to only consider pairs of methods which
-- are not parallel composable (and thus, use the list which was already
-- filtered for "verifySafeActions"), because methods which have a rule
-- between them are not parallel composable.

verifyStaticScheduleOneRule ::
    ErrorHandle -> Flags -> Maybe Backend ->
    RuleBetweenMap -> RulePCConflictUseMap ->
    SM (Maybe Backend)
verifyStaticScheduleOneRule errh flags gen_backend
                            ruleBetweenMap rulePCConflictUseMap =
    let
        -- for one-rule checking, a rule between the method in either order
        -- is an error, so look up both directions
        findBetween m1 m2 =
            case (M.lookup (m1,m2) ruleBetweenMap) of
                Nothing  -> M.lookup (m2,m1) ruleBetweenMap
                Just res -> Just res

        checkOneRule ::
            (ARuleId, (AExpr, MethodUsesList, PCConflictPairsMap))
            -> Maybe (ARuleId, [(MethodId, MethodId, [ARuleId])])
        checkOneRule (rule, (_, _, usePairsMap)) =
           let
               badPairs = [ (m1,m2,rs)
                              | (inst, usePairs) <- M.toList usePairsMap,
                                ((methId1,_), (methId2,_)) <- usePairs,
                                let m1 = MethodId inst methId1,
                                let m2 = MethodId inst methId2,
                                -- either direction is an error
                                let m_rs = findBetween m1 m2,
                                (Just rs) <- [m_rs] ]
           in  if (null badPairs)
               then Nothing
               else Just (rule, badPairs)

        err_pairs = mapMaybe checkOneRule (M.toList rulePCConflictUseMap)

        mkErr (r, ms) =
            let mkPair (m1, m2, rs) = (pfpString m1, pfpString m2,
                                       map pfpString rs)
            in  (getPosition r,
                 EDynamicExecOrderOneRule (pfpString r) (map mkPair ms))

        errs = map mkErr err_pairs
    in
        if (null errs)
        then return gen_backend
        else
            if (backend flags == Just Bluesim)
            then throwError (EMsgs errs)
            else convEM errh $
                     -- taint the .ba file to be just for Verilog
                     EMWarning errs (Just Verilog)

-- ----------
-- verifyStaticScheduleTwoRules

-- Go through all pairs of rules (or methods) of a module and check
-- that all pairs of method calls (on the same state) can be composed
-- with a static schedule.

-- Note that rule-between-methods is already accounted for in the conflict
-- info for those methods, so pairs of rules/methods whose execution order
-- already takes into account all method call pairs are OK.  We only need
-- to check those rule/method pairs where the method calls were not taken
-- into account: (1) the rule predicates are disjoint (CAN_FIRE is disjoint),
-- (2) the rules/methods are made to conflict (WILL_FIRE is disjoint),
-- or (3) some method call pairs were ignored because the conditions of the
-- calls were disjoint.  The first two are determined by consulting the DB;
-- the third is passed in as a set.

-- We also return rule pairs used to create some arbitrary choice edges,
-- so that we can be sure that, where possible, the arbitrary
-- ordering choices between pairs of (asserted) ME and CF rules
-- do not conflict with the ordering required for a static schedule
-- Any rule pairs whose implied edge creates a cycle are suppressed
-- (since those rule pairs taint the backend by requiring dynamic scheduling)
-- However, even if the backend is tainted, we return all safe rule pairs,
-- to minimize Bluesim/Verilog differences

verifyStaticScheduleTwoRules ::
    ErrorHandle -> Flags -> Maybe Backend -> AId ->
    RuleBetweenMap -> RuleMethodUseMap ->
    [ARuleId] -> ExclusiveRulesDB -> RuleDisjointTest ->
    S.Set (ARuleId, ARuleId) ->
    ReachableMap -> CSMap -> [(CSNode,[CSNode])] -> SchedOrdMap ->
    SM (Maybe Backend, [(CSNode, CSNode, CSEdge)])
verifyStaticScheduleTwoRules errh flags gen_backend moduleId
                             ruleBetweenMap ruleMethodUseMap
                             ruleNames erdb cf_rules_test setToTest
                             reachmap seq_map seq_graph sched_id_order =
    let
        -- avoid duplicate messages by applying to a whole list
        checkOneRule ::
            [(ARuleId, (AExpr, M.Map AId [(AId, AExpr)]))] ->
            [Either EMsg (ARuleId, ARuleId, [(MethodId, MethodId)])]
        checkOneRule ((r1, (_, r1_usemap)):rest) =
          let
              r2s = map fst rest

              excl_or_cf r1 r2 = areRulesExclusive erdb r1 r2 ||
                                 cf_rules_test r1 r2

              checkSecondRule ::
                  ARuleId ->
                  [Either EMsg (ARuleId, ARuleId, [(MethodId, MethodId)])]
              checkSecondRule r2 | ( (r1 == r2) ||
                                     not ((excl_or_cf r1 r2) ||
                                          (S.member (r1, r2) setToTest))
                                   )
                                 = []
              checkSecondRule r2 =
                let
                    r2_usemap =
                        case (M.lookup r2 ruleMethodUseMap) of
                            Just (_, res) -> res
                            Nothing -> internalError
                                         ("verifyStaticScheduleTwoRules: " ++
                                          "r2_usemap: " ++ getIdString r2)

                    checkOneInstance ::
                        (AId, [(AId, AExpr)]) ->
                        -- Left indicates (r1,r2), Right indicates (r2,r1)
                        [Either ((MethodId, MethodId), [ARuleId])
                                ((MethodId, MethodId), [ARuleId])]
                    checkOneInstance (inst, methods1) =
                        let
                            lookupRule m1 m2 =
                              case (M.lookup (m1,m2) ruleBetweenMap) of
                                Just rs -> [Left ((m1,m2),rs)]
                                Nothing ->
                                  case (M.lookup (m2,m1) ruleBetweenMap) of
                                    Just rs -> [Right ((m1,m2),rs)]
                                    Nothing -> []
                            pairs =
                              [ (m1, m2)
                                  | let m_methods2 = M.lookup inst r2_usemap,
                                    (Just methods2) <- [m_methods2],
                                    (methId1, _) <- methods1,
                                    (methId2, _) <- methods2,
                                    methId1 /= methId2,
                                    let m1 = MethodId inst methId1,
                                    let m2 = MethodId inst methId2
                              ]
                            bad_pairs_one_instance =
                              [ p | (m1,m2) <- pairs,
                                    p <- lookupRule m1 m2 ]
                        in
                            bad_pairs_one_instance
                    bad_pairs_one_rule =
                        concatMap checkOneInstance (M.toList r1_usemap)
                    (left_pairs, right_pairs) = separate bad_pairs_one_rule

                    pfpMethUse ((m1,m2),rs) = (pfpString m1, pfpString m2,
                                               map pfpString rs)

                    -- check for an error in the given direction
                    check_err r1 r2 uses =
                      case (M.lookup (mkCSNExec sched_id_order r1) reachmap) of
                        Nothing -> [Right (r2, r1, map fst uses)]
                        Just reachables ->
                          case (lookup (mkCSNExec sched_id_order r2) reachables) of
                            Nothing -> [Right (r2, r1, map fst uses)]
                            Just raw_path ->
                              let -- the path is in reverse
                                  path = reverse raw_path
                                  (expl_doc, path_strs) =
                                      mkPathExplanation seq_map path
                              in
                                  [Left (getPosition r1,
                                         EDynamicExecOrderTwoRules
                                          (pfpString r1) (pfpString r2)
                                          (map pfpMethUse uses)
                                          path_strs expl_doc)]

                    -- left error
                    -- method use requires (r1 before r2) so check in graph
                    -- for (r2 before r1)
                    check_left_err = check_err r2 r1 left_pairs

                    -- right error
                    -- method use requires (r2 before r1) so check in graph
                    -- for (r1 before r2)
                    check_right_err = check_err r1 r2 right_pairs
                in
                    if (not (null left_pairs))
                    then if (not (null right_pairs))
                         then -- bidirectional error
                              [Left (getPosition r1,
                                     EDynamicExecOrderTwoRulesBothDir
                                      (pfpString r1) (pfpString r2)
                                      (map pfpMethUse left_pairs)
                                      (map pfpMethUse right_pairs))]
                         else check_left_err
                    else if (not (null right_pairs))
                         then check_right_err
                         else []
          in
              concatMap checkSecondRule r2s ++ checkOneRule rest
        checkOneRule [] = []

        (pair_errs, raw_edges) =
            separate $ checkOneRule (M.toList ruleMethodUseMap)

        edges = [ (mkCSNExec sched_id_order r1, mkCSNExec sched_id_order r2, CSE_Conflict [CArbitraryChoice])
                      | (r1, r2, _) <- raw_edges ]

        -- Because the reachmap was not updated incrementally as new edges
        -- were added, a loop could have been created with two or more new
        -- edges.  Rather than update the reachmap incrementally, we can
        -- just look for a cycle in the graph plus the new edges -- relying
        -- on the graph being cycle-free (if there was a cycle, it was
        -- already reported as an error to the user)
        --
        -- Note: We could avoid using the reachmap entirely by not
        -- erroring in "checkSecondRule" above, but always creating an
        -- edge and then looking for a cycle at the end (as we do here).
        -- This simplifies everything into one process, but it may be nice
        -- to report the errors the different types of errors this way.
        -- XXX How hard would it be to detect the different cases?
        cycle_errs = checkCSGraphWithDynamicSchedEdges moduleId
                         raw_edges edges seq_map seq_graph sched_id_order


        errs = pair_errs ++ cycle_errs
    in
        if (null errs)
        then return (gen_backend, edges)
        else
            if (backend flags == Just Bluesim)
            then throwError (EMsgs errs)
            else convEM errh $
                     -- taint the .ba file to be just for Verilog
                     -- and don't return any edges
                     EMWarning errs (Just Verilog, [])


-- See if the new edges create any cycles and, if so, report them as errors
checkCSGraphWithDynamicSchedEdges :: AId ->
    [(ARuleId, ARuleId, [(MethodId, MethodId)])] ->
    [(CSNode, CSNode, CSEdge)] ->
    CSMap -> [(CSNode, [CSNode])] -> SchedOrdMap ->
    [EMsg]
checkCSGraphWithDynamicSchedEdges moduleId raw_edges edges seq_map seq_graph sched_id_order =
    let seq_graph_new = addEdgesToCSGraph edges seq_graph
        seq_map_new = foldl G.addWeakEdge seq_map edges
    in  case (tsort seq_graph_new) of
          Right _ -> []
          Left sccs -> errCSDynamicCycles moduleId raw_edges seq_map_new sched_id_order sccs

errCSDynamicCycles ::
    AId -> [(ARuleId, ARuleId, [(MethodId, MethodId)])] ->
    CSMap -> SchedOrdMap -> [[CSNode]] -> [EMsg]
errCSDynamicCycles moduleId edges seq_map sched_id_order sccs = map errCSDynamicCycle sccs
  where
    edge_map = M.fromList [ ((mkCSNExec sched_id_order r1, mkCSNExec sched_id_order r2), uses)
                            | (r1, r2, uses) <- edges ]

    errCSDynamicCycle :: [CSNode] -> EMsg
    errCSDynamicCycle scc =
        let path = GU.extractOneCycle_gmap seq_map scc

            -- the edges along the path
            path_edges = GU.findPathEdges seq_map path
            -- remove the SchedBeforeExec edges, because they are not
            -- informative to the user
            path_edges' = filterSchedBeforeExec path_edges

            -- an explanation for each edge
            expl_doc = map mkExpl path_edges'
            mkExpl :: ((CSNode, CSNode), CSEdge) -> Doc
            mkExpl (p@(n1,n2), e) =
                -- since we didn't use a special tag for the new edges,
                -- look them up and print them specially
                case (M.lookup p edge_map) of
                  Just uses ->
                    let pair = (getCSNId n1, getCSNId n2)
                        txt = "execution order because of calls to " ++
                              "methods with rules between them:"
                        meths = vcat [pfp m1 <+> text "vs." <+> pfp m2
                                      | (m1, m2) <- uses]
                    in  fsep [pfp pair, s2par txt, nest 2 meths]
                  Nothing -> printCSEdgePair p e

            -- the names of the nodes in the path (after filtering)
            path_ids = map (getCSNId . fst . fst) path_edges'
            -- report the path such that start and end node are the same
            path_ids' = path_ids ++ [headOrErr "errCSCycle" path_ids]
            path_strs = map pfpString path_ids'
        in
            (getPosition moduleId,
             EDynamicExecOrderTwoRulesLoop path_strs expl_doc)


-- ========================================================================
-- Check that a rule marked (* can_schedule_first *) does not require
-- a rule in another module to execute before it.

-- ----------
-- RuleBeforeMap

type RuleBeforeMap = M.Map MethodId [Either ARuleId AMethodId]

-- make a lookup of rules which must execute before a method
makeRuleBeforeMap :: [AVInst] -> RuleBeforeMap
makeRuleBeforeMap avis =
    M.fromList $ [ (m,rs)
                 | avi <- avis
                 , let instId = avi_vname avi
                 , let rbi = rulesBeforeMethods (vSched (avi_vmi avi))
                 , (methId, rs) <- rbi
                 , let m = MethodId instId methId
                 ]

-- ----------
-- makeUnsyncSet

-- make a set containing all sub-instance methods which are unsynchronized
-- clock domain crossings.
makeUnsyncSet :: [AVInst] -> S.Set MethodId
makeUnsyncSet avis =
    S.fromList $ [ MethodId instId methId
                 | avi <- avis
                 , let instId = avi_vname avi
                 , let ccm = clockCrossingMethods (vSched (avi_vmi avi))
                 , methId <- ccm
                 ]

-- ========================================================================
-- Check for paths from a method's Sched node to its Exec node
--
-- If there is a path other than via the direct edge, then this causes
-- problems when merging schedules, because the two nodes collapse into
-- the exec node of the calling rule.
--

-- This has a lot of code similar to "mkTestForRuleBetweenMethods",
-- but differs in that we need to keep outgoing method edges.  Also,
-- we are looking specifically to start from a method Sched node and
-- arrive back at the Exec node (not Exec or Sched) of the same method
-- (not of a different method).  (Technically, we can't arrive back at
-- the Sched node anyway, because cycles have been removed.)

checkMethodCycles :: AId -> [AId] -> ReachableMap -> CSMap -> SchedOrdMap -> SM ()
checkMethodCycles moduleId ifcRuleNames reachmap seq_map sched_id_order = do
  let
      -- for efficiency of lookup, make the ifc names a set
      ifc_id_set = S.fromList ifcRuleNames
      isMethodId i = i `S.member` ifc_id_set

      meth_sched_outgoing_edges =
          [ (i, n) | i <- ifcRuleNames,
                     n <- G.neighbors seq_map (mkCSNSched sched_id_order i),
                     -- don't include the path to the exec
                     n /= (mkCSNExec sched_id_order i) ]

      -- XXX this could be constructed by mapping a function onto the
      -- XXX existing "seq_map"; would that be more efficient?
      -- make the outgoing edges easily searchable
      meth_outgoing_edges_map :: M.Map AId [CSNode]
      meth_outgoing_edges_map =
          M.fromList $ joinByFst $ meth_sched_outgoing_edges

      findOutgoingSchedEdges m =
          -- if it's not in the map, there are no outgoing edges
          fromMaybe [] (M.lookup m meth_outgoing_edges_map)

      -- like the reachmap, but only keep the reachable method Exec nodes
      -- (and filter out empty reachables?)
      reachable_meth_exec_map :: M.Map CSNode [(AId, [CSNode])]
      reachable_meth_exec_map =
          let -- only keep the reachable method Exec nodes
              -- (and remove keys which are left with an empty reachables list)
              prune_reachables rs =
                  let rs' = [ (i,ps) | r@(CSN_Exec i _, ps) <- rs, isMethodId i ]
                  in  if (null rs')
                      then Nothing
                      else Just rs'
          in  M.mapMaybe prune_reachables reachmap

      findReachableMethExecs n =
          fromMaybe [] (M.lookup n reachable_meth_exec_map)

      hasSchedToExecPath m =
        let
            out_rs = findOutgoingSchedEdges m
            reachable_methods = concatMap findReachableMethExecs out_rs
        in
            case (lookup m reachable_methods) of
               Nothing -> Nothing
               Just raw_path -> -- the path is in reverse
                                -- and add the final node to the front,
                                -- to make it a cycle
                                Just (m, mkCSNSched sched_id_order m : reverse raw_path)

      -- bad methods
      bad_meths :: [(AId,[CSNode])]
      bad_meths = mapMaybe hasSchedToExecPath ifcRuleNames

      mkMethSchedErr :: (AId,[CSNode]) -> EMsg
      mkMethSchedErr (meth, path_nodes) =
          let
              -- make the explanation doc
              (expl_doc, path_strs) = mkPathExplanation seq_map path_nodes
          in
              (getPosition meth, -- getPosition moduleId ?
               EMethodSchedToExec (pfpString meth) path_strs expl_doc)

  when (not (null bad_meths)) $
      throwError (EMsgs (map mkMethSchedErr bad_meths))


-- ========================================================================
-- generate the reachability graph for the final combined graph (no ffunc)
-- including edges through methods

-- Unlike computing SchedInfo where we don't want to find reachable nodes
-- through methods, this computes reachabilities based on ALL edges.
-- It is used by "checkMethodCycles" to check for Bug 1363 and by
-- "verifyStaticScheduleTwoRules" to check for Bug 1401.

type ReachableMap = M.Map CSNode [(CSNode, [CSNode])]

mkReachableMap :: [AId] -> [AId] -> [(CSNode,[CSNode])] -> SchedOrdMap -> IO ReachableMap
mkReachableMap ifcRuleNames userRuleNames seq_graph sched_id_order = do
  let
      all_ids = ifcRuleNames ++ userRuleNames

      seq_s_nodes, seq_e_nodes, seq_nodes :: [CSNode]
      seq_s_nodes = [ mkCSNSched sched_id_order i | i <- all_ids ]
      seq_e_nodes = [ mkCSNExec  sched_id_order i | i <- all_ids ]
      seq_nodes = seq_s_nodes ++ seq_e_nodes

      -- the edges of seq_graph expressed individually
      -- (reversed to put them in SB order: (n1,n2) => n1 happen before n2)
      seq_edges :: [(CSNode, CSNode)]
      seq_edges = [ (r2, r1) | (r1, r2s) <- seq_graph, r2 <- r2s ]

  --seq_reachables :: [(CSNode, [(CSNode, [CSNode])])]
  seq_reachables <- do
      seq_path_graph <- GW.makeGraph seq_nodes seq_edges
      reachables <- GW.findReachablesIO seq_path_graph seq_nodes
      return (zip seq_nodes reachables)

  -- filter out the empty reachables
  let seq_reachables_filtered = filter (not . null . snd) seq_reachables

  return (M.fromList seq_reachables_filtered)

-- ----------

-- Make an explanation Doc for a path of nodes
-- Returns a Doc explaining the path and a list of the names of the nodes
-- the path (Sched and Exec are dropped, just the name of the rule/method)
mkPathExplanation :: CSMap -> [CSNode] -> ([Doc], [String])
mkPathExplanation seq_map path_nodes =
    let
        path_node_pairs :: [(CSNode, CSNode)]
        path_node_pairs =
            zip path_nodes (tailOrErr "mkPathExplanation" path_nodes)
        mkPairEdge :: (CSNode, CSNode) -> ((CSNode, CSNode), CSEdge)
        mkPairEdge p =
            case G.lookup p seq_map of
                Just e -> (p, e)
                Nothing -> internalError ("mkPathExplanation: " ++
                                          "not found: " ++ ppReadable p)
                                          --show path_nodes ++
                                          --ppReadable (G.toList seq_map))
        path_edges = filterSchedBeforeExec $
                         map mkPairEdge path_node_pairs
        expl_doc = map (\ (p,e) -> printCSEdgePair p e) path_edges

        -- the names of the nodes in the path (after filtering)
        path_ids = -- the start of each edge
                   map (getCSNId . fst . fst) path_edges ++
                   -- plus the end of the last edge
                   [getCSNId
                       (snd (fst (lastOrErr "mkPathExplanation" path_edges)))]
        path_strs = map pfpString path_ids
    in
        (expl_doc, path_strs)

-- ========================================================================
-- generate DOT graphs

-- generic dumping function
dumpDOTGraph :: ErrorHandle -> Flags ->
                String -> String -> String -> DOTGraph -> IO ()
dumpDOTGraph errh flags prefix modName suffix graph = do
    let contents = printDOTGraph graph
        basename = modName ++ "_" ++ suffix
    dotName <- genFileName mkDOTName (infoDir flags) prefix basename
    let dotNameRel  = getRelativeFilePath dotName
        dotNameFull = getFullFilePath dotName
    -- write file
    writeFileCatch errh dotNameFull contents
    -- tell user that the file was written
    putStrLnF ("DOT file created: " ++ dotNameRel)

-- ----------

dumpConflictMapDOT :: ErrorHandle -> Flags -> String -> AId ->
                      [AId] -> [AId] -> ConflictMap -> IO ()
dumpConflictMapDOT errh flags prefix modId
                   ifcRuleNames userRuleNames cmap = do
    timeStr <- mkTimestampComment flags
    let modName = getIdBaseString modId
        graph = conflictMapToDOT flags timeStr modName
                                 ifcRuleNames userRuleNames cmap
    dumpDOTGraph errh flags prefix modName "conflict" graph


conflictMapToDOT :: Flags -> String -> String -> [AId] -> [AId] ->
                    ConflictMap -> DOTGraph
conflictMapToDOT flags timeStr modName ifcRuleNames userRuleNames cmap =
    let
        ruleNames = ifcRuleNames ++ userRuleNames
        node_stmts = [ Node (getIdString i) [NShape NBox]
                       | i <- ifcRuleNames ] ++
                     [ Node (getIdString i) [NShape NEllipse]
                       | i <- userRuleNames ]
        mkEdges (r1:rs) =
            let r1name = getIdString r1
                mkE r2
                    -- (r1,r2) in the map means r1 cannot seq before r2
                  | (r1,r2) `G.member` cmap && (r2,r1) `G.member` cmap =
                      -- total conflict
                      [Edge [r1name, getIdString r2] [EStyle EBold, EDir ENone]]
                  | (r1,r2) `G.member` cmap =
                      -- r2 SB r1
                      [Edge [getIdString r2, r1name] [EStyle EDashed]]
                  | (r2,r1) `G.member` cmap =
                       -- r1 SB r2
                      [Edge [r1name, getIdString r2] [EStyle EDashed]]
                  | otherwise = [] -- no conflict
            in  (concatMap mkE rs) ++ (mkEdges rs)
        mkEdges [] = []
        edge_stmts = mkEdges ruleNames
        graph_label =
            -- in escaped string format
            doubleQuote
                ("Conflict graph for module " ++
                 "\\\"" ++ modName ++ "\\\"\\n" ++
                 "Generated by " ++ bscVersionStr (showVersion flags) ++ "\\n" ++
                 timeStr)
        graph_attrs = [GraphAttr (GLabel graph_label)]
        stmts = node_stmts ++ edge_stmts ++ graph_attrs
    in
        DOTGraph True True (Just "conflicts") stmts

-- ----------

dumpExecGraphDOT :: ErrorHandle -> Flags -> String -> AId ->
                    [AId] -> [AId] -> [(AId,[AId])] -> IO ()
dumpExecGraphDOT errh flags prefix modId
                 ifcRuleNames userRuleNames scgraph = do
    timeStr <- mkTimestampComment flags
    let modName = getIdBaseString modId
        graph = execGraphToDOT flags timeStr modName
                               ifcRuleNames userRuleNames scgraph
    dumpDOTGraph errh flags prefix modName "exec" graph


execGraphToDOT :: Flags -> String -> String -> [AId] -> [AId] ->
                  [(AId,[AId])] -> DOTGraph
execGraphToDOT flags timeStr modName ifcRuleNames userRuleNames scgraph =
    let
        node_stmts = [ Node (getIdString i) [NShape NBox]
                       | i <- ifcRuleNames ] ++
                     [ Node (getIdString i) [NShape NEllipse]
                       | i <- userRuleNames ]
        mkEdges (r1,r2s) =
            let r1name = getIdString r1
                -- (r1,r2) means r2 SB r1
                -- XXX we could make the edges gray, to stand out from
                -- XXX the nodes; of course, the user can add one line to
                -- XXX file to do this himself
                edges = [ Edge [getIdString r2, r1name] []
                            | r2 <- r2s ]
            in  edges
        edge_stmts = concatMap mkEdges scgraph
        graph_label =
            -- in escaped string format
            doubleQuote
                ("Execution order graph for module " ++
                 "\\\"" ++ modName ++ "\\\"\\n" ++
                 "Generated by " ++ bscVersionStr (showVersion flags) ++ "\\n" ++
                 timeStr)
        graph_attrs = [GraphAttr (GLabel graph_label)]
        stmts = node_stmts ++ edge_stmts ++ graph_attrs
    in
        DOTGraph True True (Just "execution order") stmts

-- ----------

dumpUrgencyGraphDOT :: ErrorHandle -> Flags -> String -> AId ->
                       [AId] -> [AId] -> UrgencyMap -> IO ()
dumpUrgencyGraphDOT errh flags prefix modId
                    ifcRuleNames userRuleNames umap = do
    timeStr <- mkTimestampComment flags
    let modName = getIdBaseString modId
        graph = urgencyGraphToDOT flags timeStr modName
                                  ifcRuleNames userRuleNames umap
    dumpDOTGraph errh flags prefix modName "urgency" graph


urgencyGraphToDOT :: Flags -> String -> String -> [AId] -> [AId] ->
                     UrgencyMap -> DOTGraph
urgencyGraphToDOT flags timeStr modName ifcRuleNames userRuleNames umap =
    let
        node_stmts = [ Node (getIdString i) [NShape NBox]
                       | i <- ifcRuleNames ] ++
                     [ Node (getIdString i) [NShape NEllipse]
                       | i <- userRuleNames ]
        mkEdges (r1,r2s) =
            let r1name = getIdString r1
                -- (r1,r2) means r1 more urgent than r2
                -- XXX we could make the edges gray, to stand out from
                -- XXX the nodes; of course, the user can add one line to
                -- XXX file to do this himself
                edges = [ Edge [r1name, getIdString r2] []
                            | (r2,_) <- r2s ]
            in  edges
        edge_stmts = concatMap mkEdges (G.toList umap)
        graph_label =
            -- in escaped string format
            doubleQuote
                ("Urgency order graph for module " ++
                 "\\\"" ++ modName ++ "\\\"\\n" ++
                 "Generated by " ++ bscVersionStr (showVersion flags) ++ "\\n" ++
                 timeStr)
        graph_attrs = [GraphAttr (GLabel graph_label)]
        stmts = node_stmts ++ edge_stmts ++ graph_attrs
    in
        DOTGraph True True (Just "urgency order") stmts

-- ----------

dumpCombinedGraphDOT :: ErrorHandle -> Flags -> String -> AId ->
                        [AId] -> [AId] -> [(CSNode,[CSNode])] -> IO ()
dumpCombinedGraphDOT errh flags prefix modId
                     ifcRuleNames userRuleNames seq_graph = do
    timeStr <- mkTimestampComment flags
    let modName = getIdBaseString modId
        graph = combinedGraphToDOT flags timeStr modName
                                   ifcRuleNames userRuleNames seq_graph
    dumpDOTGraph errh flags prefix modName "combined" graph


combinedGraphToDOT :: Flags -> String -> String -> [AId] -> [AId] ->
                      [(CSNode,[CSNode])] ->
                      DOTGraph
combinedGraphToDOT flags timeStr modName ifcRuleNames userRuleNames seq_graph =
    let
        mkSchedName i = doubleQuote ("Sched " ++ getIdString i)
        mkExecName i = doubleQuote ("Exec " ++ getIdString i)
        mkNodeName (CSN_Sched i _) = mkSchedName i
        mkNodeName (CSN_Exec  i _) = mkExecName i

        mkSchedNode isMethod i =
            let name = mkSchedName i
                shape = if isMethod then NBox else NEllipse
            in  Node name [NStyle NFilled, NShape shape]
        mkExecNode isMethod i =
            let name = mkExecName i
                shape = if isMethod then NBox else NEllipse
            in  Node name [NShape shape]
        node_stmts = [ n | i <- ifcRuleNames,
                           n <- [ mkSchedNode True i, mkExecNode True i ] ] ++
                     [ n | i <- userRuleNames,
                           n <- [ mkSchedNode False i, mkExecNode False i ] ]

        mkEdges (n1,n2s) =
            let n1name = mkNodeName n1
                -- (n1,n2) means n2 before n1
                -- XXX we could do more with the edge attributes
                edges = [ Edge [mkNodeName n2, n1name] []
                            | n2 <- n2s ]
            in  edges
        edge_stmts = concatMap mkEdges seq_graph

        graph_label =
            -- in escaped string format
            doubleQuote
                ("Combined scheduling graph for module " ++
                 "\\\"" ++ modName ++ "\\\"\\n" ++
                 "Generated by " ++ bscVersionStr (showVersion flags) ++ "\\n" ++
                 timeStr)
        graph_attrs = [GraphAttr (GLabel graph_label)]

        stmts = node_stmts ++ edge_stmts ++ graph_attrs
    in
        DOTGraph True True (Just "combined") stmts

-- ----------

dumpCombinedGraphFullDOT :: ErrorHandle -> Flags -> String -> AId ->
                            [AId] -> [AId] -> CSMap -> IO ()
dumpCombinedGraphFullDOT errh flags prefix modId
                         ifcRuleNames userRuleNames seq_map = do
    timeStr <- mkTimestampComment flags
    let modName = getIdBaseString modId
        graph = combinedGraphFullToDOT flags timeStr modName
                                       ifcRuleNames userRuleNames seq_map
    dumpDOTGraph errh flags prefix modName "combined_full" graph


combinedGraphFullToDOT :: Flags -> String -> String -> [AId] -> [AId] ->
                          CSMap -> DOTGraph
combinedGraphFullToDOT flags timeStr modName ifcRuleNames userRuleNames seq_map =
    let
        isArbEdge (CSE_Urgency e)  = isArbUrgEdge e
        isArbEdge (CSE_Conflict e) = any isArbExecEdge e
        isArbEdge (CSE_SchedBeforeExec) = False
        isArbUrgEdge (UEArbitraryChoice) = True
        isArbUrgEdge _ = False
        isArbExecEdge (CArbitraryChoice) = True
        isArbExecEdge (CFFuncArbitraryChoice) = True
        isArbExecEdge _ = False

        mkSchedName i = doubleQuote ("Sched " ++ getIdString i)
        mkExecName i = doubleQuote ("Exec " ++ getIdString i)
        mkNodeName (CSN_Sched i _) = mkSchedName i
        mkNodeName (CSN_Exec  i _) = mkExecName i

        mkSchedNode isMethod i =
            let name = mkSchedName i
                shape = if isMethod then NBox else NEllipse
            in  Node name [NStyle NFilled, NShape shape]
        mkExecNode isMethod i =
            let name = mkExecName i
                shape = if isMethod then NBox else NEllipse
            in  Node name [NShape shape]
        node_stmts = [ n | i <- ifcRuleNames,
                           n <- [ mkSchedNode True i, mkExecNode True i ] ] ++
                     [ n | i <- userRuleNames,
                           n <- [ mkSchedNode False i, mkExecNode False i ] ]

        mkEdges (n1,n2s) =
            let n1name = mkNodeName n1
                mkAttr e = if (isArbEdge e)
                           then [EStyle EBold, EColor "blue"]
                           else []
                -- (n1,n2) means n1 before n2
                -- XXX we could do more with the edge attributes
                edges = [ Edge [n1name, mkNodeName n2] (mkAttr e)
                            | (n2,e) <- n2s ]
            in  edges
        edge_stmts = concatMap mkEdges (G.toList seq_map)

        graph_label =
            -- in escaped string format
            doubleQuote
                ("Full combined scheduling graph for module " ++
                 "\\\"" ++ modName ++ "\\\"\\n" ++
                 "Edges inserted by the compiler are higlighted in blue and bold\\n" ++
                 "Generated by " ++ bscVersionStr (showVersion flags) ++ "\\n" ++
                 timeStr)
        graph_attrs = [GraphAttr (GLabel graph_label)]

        stmts = node_stmts ++ edge_stmts ++ graph_attrs
    in
        DOTGraph True True (Just "combined (full)") stmts


-- ========================================================================
-- Utility functions
--

-- --------------------

{-
-- This was used to mix up the urgency order by merging rules in
-- alphabetical order.  No longer needed since we warn about
-- arbitrary rule urgency decisions.
alphaMerge :: [ARuleId] -> [ARuleId] -> [ARuleId]
alphaMerge []     ys   = ys
alphaMerge xs     []   = xs
alphaMerge xxs@(x:xs) yys@(y:ys)
    | getIdString x <= getIdString y = x : alphaMerge xs yys
    | otherwise        = y : alphaMerge xxs ys
-}

-- --------------------

pfp :: (PPrint a, PVPrint a) => a -> Doc
pfp = pfPrint PDReadable 0

-- --------------------

-- #############################################################################
-- # ME Assumps code
-- #############################################################################

addAllMEAssumps :: [ASchedulePragma] -> [ARule] -> ([ARule],[(ARuleId,[ARuleId])])
addAllMEAssumps pragmas rules =
  let new_id i = addSuffix (mk_homeless_id "__me_check") i
      pairs = concat (zipWith (addMEAssumps pragmas) rules (map new_id [0..]))
      (new_rules, orders) = unzip pairs
  in (new_rules, orders)

addMEAssumps :: [ASchedulePragma] -> ARule -> ARuleId -> [(ARule,(ARuleId,[ARuleId]))]
addMEAssumps pragmas r@(ARule { arule_id = rid }) new_id = rs
  where me_pairs = extractMEPairsSP pragmas
        getRule ids = headOrErr "addMEAssumps getRule" ids
        check_pairs :: [(ARuleId, [([ARuleId],[ARuleId])])]
        check_pairs = [ ((getRule (as ++ bs)), [(as, bs)]) | (as, bs) <- me_pairs ]
        check_map = M.fromListWith (++) check_pairs
        rs = case (M.lookup rid check_map) of
                   Nothing  -> []
                   Just mes -> let (assumps, ids) = unzip (concatMap mkMEAssump mes)
                                   id_list = concat ids
                               in if (length id_list < 2)
                                   then []
                                   else [(r { arule_id = new_id,
                                              arule_pred = aTrue,
                                              arule_actions = [],
                                              arule_assumps = assumps }, (new_id, id_list))]

mkMEAssump :: ([Id], [Id]) -> [(AAssumption, [Id])]
mkMEAssump ([], _) = []
mkMEAssump (_, []) = []
mkMEAssump (aids, bids) = -- trace("ME: " ++ (ppReadable aids) ++ " " ++ (ppReadable bids)) $
                          [(AAssumption p ea, (aids ++ bids))]
  where p   = aAnd (aOrs (map (aBoolVar . mkIdWillFire) aids)) (aOrs (map (aBoolVar . mkIdWillFire) bids))
        ea  = [errAction str]
        str = showErrorList [(getPosition aids, EMutuallyExclusiveRulesFire (ppReadable aids) (ppReadable bids))]

errAction :: String -> AAction
errAction msg = AFCall idErrorTask "$error" False [aTrue, ASStr defaultAId ty msg] True
  where ty = ATString (Just (genericLength msg))

getNextRule :: ARuleId -> (M.Map ARuleId (Maybe ClockDomain)) -> [ARuleId] -> (Maybe ARuleId)
getNextRule r rd_map (r0:r1:rest) | r == r0 =
  let d0 = M.findWithDefault Nothing r0 rd_map
      d1 = M.findWithDefault Nothing r1 rd_map
  in if (d0 == d1) then (Just r1) else getNextRule r rd_map (r0:rest)

getNextRule r rd_map (_:rest) = getNextRule r rd_map rest
getNextRule r rd_map [] = Nothing
