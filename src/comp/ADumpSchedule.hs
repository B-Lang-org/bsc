-- TODO:
--   The schedule should always print to a file, and not just stdout.
--   aDumpSchedule should be refactored to meet coding standards

{-# LANGUAGE CPP #-}
module ADumpSchedule(
                     MethodDumpInfo,
                     aDumpSchedule,
                     aDumpScheduleErr,
                     genMethodDumpMap,
                     dumpMethodInfo,
                     dumpMethodBVIInfo
                    ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Control.Monad(unless, when, foldM)
import System.IO(IOMode(..), hPutChar, hClose, stdout, hFlush)
import Data.Maybe(fromMaybe)
import Data.List(delete, find)
import qualified Data.Set as S

import ASyntax
import Error(internalError, showWarningList, getErrMsgTag, ErrMsg(..),
             ErrorHandle, bsWarning, emptyContext)
import Id
import SAT(initSATState, checkEq)
import VModInfo(VSchedInfo)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import AScheduleInfo
import ADumpScheduleInfo
import Flags(Flags, quiet, showSchedule, removeStarvedRules, infoDir, hasDump, DumpFlag(..))
import Position
import Pragma
import PFPrint
import FileNameUtil(mkSchedName, getRelativeFilePath)
import FileIOUtil(putStrHandles, openFileCatch)

-- import Debug.Trace

str_none :: String
str_none = "(none)"

list_or_none :: [a] -> Doc -> Doc
list_or_none l doc =
  if (not . null) l then doc else text str_none

-- convert scheduling group into list of rules and blocking rules
ruleBlockers :: AScheduler -> [(ARuleId, [ARuleId])]
ruleBlockers (ASchedEsposito espositoSch) = espositoSch

dumpRule :: Flags -> [ADef] -> (ARuleId, AExpr, Maybe [ARuleId]) -> Doc
dumpRule flags ds (rid, predicate, maybe_blockers) =
  text ("Rule:") <+> text (dropRulePrefix rid) $$
  text ("Predicate:") <+> (pPrintExpandFlags flags ds PDReadable bContext predicate) $$
  (case maybe_blockers of
     Just blockers ->
         text ("Blocking rules:") <+> (list_or_none
                                         blockers
                                         (sepList (map (text . dropRulePrefix)
                                                   blockers) comma))
     Nothing -> empty
   ) $$
  space -- insert blank line

-- flags aren't really necessary, but dumpMethod wants them
dumpMethodInfo :: Flags -> MethodDumpInfo -> [Doc]
dumpMethodInfo flags [] = [text str_none] -- show that there is no information
dumpMethodInfo flags mdis = map (dumpMethod flags False []) mdis

dumpMethod :: Flags -> Bool -> [ADef] -> (AMethodId, AExpr, [(AMethodId, RuleConflictType)]) -> Doc
dumpMethod flags dumpRdy ds (mid, p, clist) =
  let cf_lst        = [rid | (rid, cftype) <- clist, cftype == ConflictFree]
      scbefore_lst  = [rid | (rid, cftype) <- clist, cftype == SCBefore]
      scafter_lst   = [rid | (rid, cftype) <- clist, cftype == SCAfter]
      scbeforeR_lst = [rid | (rid, cftype) <- clist, cftype == SCBeforeR]
      scafterR_lst  = [rid | (rid, cftype) <- clist, cftype == SCAfterR]
      conflict_lst  = [rid | (rid, cftype) <- clist, cftype == Complete]
      plist str lst = if (not . null) lst
                      then (text str <+> (sepList (map (text . pfpString)
                                                   lst) comma))
                      else empty
  in
    text ("Method:") <+> text (getFromReady mid) $$
    (if dumpRdy
     then text ("Ready signal:") <+> (pPrintExpandFlags flags ds PDReadable bContext p)
     else empty
    ) $$
    plist "Conflict-free:" cf_lst $$
    plist "Sequenced before:" scbefore_lst $$
    plist "Sequenced before (restricted):" scbeforeR_lst $$
    plist "Sequenced after:" scafter_lst $$
    plist "Sequenced after (restricted):" scafterR_lst $$
    plist "Conflicts:" conflict_lst $$
    space -- insert blank line

dumpMethodBVIInfo :: MethodDumpInfo -> [Doc]
dumpMethodBVIInfo [] = [text str_none] -- show that there is no information
dumpMethodBVIInfo mdis = map dumpMethodBVI mdis

dumpMethodBVI :: (AMethodId, AExpr, [(AMethodId, RuleConflictType)]) -> Doc
dumpMethodBVI (mid, p, clist) =
  let cf_lst        = [rid | (rid, cftype) <- clist, cftype == ConflictFree]
      scbefore_lst  = [rid | (rid, cftype) <- clist, cftype == SCBefore]
      scbeforeR_lst = [rid | (rid, cftype) <- clist, cftype == SCBeforeR]
      conflict_lst  = [rid | (rid, cftype) <- clist, cftype == Complete]
      plist s_str e_str lst = if (not . null) lst
                      then text "schedule" <+> (text (getFromReady mid) <+> text s_str <+> (sepList (map (text . pfpString) lst) comma)) <+> (text e_str)
                      else empty
  in
    plist " CF (" ");"  cf_lst $$
    plist " SB (" ");"  scbefore_lst $$
    plist " SBR (" ");" scbeforeR_lst $$
    plist " C (" ");"   conflict_lst $$
    space -- insert blank line

aDumpSchedule :: ErrorHandle -> Flags -> [PProp] -> String ->
                 APackage -> AScheduleInfo
              -> IO (APackage, AScheduleInfo, MethodDumpInfo)
aDumpSchedule errh flags pps prefix pkg aschedinfo = do

   -- Extract fields from the package and schedinfo
   --
   let sch = asi_schedule aschedinfo
       vSchedInfo = asi_v_sched_info aschedinfo

       ifc = apkg_interface pkg
       rs = apkg_rules pkg
       ds = apkg_local_defs pkg
       ss = apkg_state_instances pkg

   let methodDumpMap = genMethodDumpMap vSchedInfo ifc
       rulePredMap  = [(rid, p) | (ARule { arule_id = rid,
                                           arule_pred = p }) <- rs ]

   let removeRules = removeStarvedRules flags

   -- Dump the schedule
   --
   when (showSchedule flags) $
       doShowSchedule errh flags prefix pkg (Right aschedinfo)
           (Just methodDumpMap) rulePredMap

   -- initial state for checking whether RDY/WILL_FIRE is constant False
   -- (rule or method will never fire)
   --
   let str = "dumpsched_" ++ ppString (apkg_name pkg)
   sat_state0 <- initSATState str errh flags True ds ss

   -- function to fold over a list of pairs of a rule/method Id and
   -- its condition, returning a list of the bad Ids, threading the state
   let checkFoldFn (bad_is, s) (i, cond) =
           do (res, s') <- checkEq s cond aFalse
              let bad_is' = if (res == Just True) then (i:bad_is) else bad_is
              return (bad_is', s')

   -- Check for methods that are never ready
   --
   let warnRdy i = (getPosition i, WMethodNeverReady (getFromReady i))
   let methodRdys = [ (mn, adef_expr v)
                    | (AIDef { aif_name = mn, aif_value = v }) <- ifc
                    , isRdyId mn
                    ]
   (falseRdys, sat_state1) <- foldM checkFoldFn ([], sat_state0) methodRdys
   -- reverse the list to put it back in order
   let rdyWarnings = map warnRdy (reverse falseRdys)

   -- Check for rules that can never fire
   --
   let warnWillFire i = (getPosition i,
                   WRuleNeverFires (dropRulePrefix i) removeRules)
   let willFireExprs = [ (i, ASDef aTBool (mkIdWillFire i))
                             | i <- (map fst rulePredMap) ]
   (falseWillFires, _) <- foldM checkFoldFn ([], sat_state1) willFireExprs
   -- reverse the list to put it back in order
   let willFireWarnings = map warnWillFire (reverse falseWillFires)

   -- Warnings
   --
   let warnings = rdyWarnings ++ willFireWarnings
   unless (null warnings) $ bsWarning errh warnings

   -- Package and schedule minus any rules that can never fire
   --
   let rs'  = [r | r@(ARule { arule_id = rid }) <- rs,
                   not (rid `elem` falseWillFires)
              ]
       ds'  = removeADefMethodPredsByRuleId falseWillFires ds
       pkg' = pkg { apkg_rules = rs',
                    apkg_local_defs = ds' }
       sch' = dropScheduleIds falseWillFires sch

   -- Return the (possibly updated) package and schedule
   -- and the method dump map
   --
   let new_pkg   = if removeRules then pkg' else pkg
       new_sched = if removeRules then sch' else sch
       new_warnings =
           let processWarning e@(pos,msg) =
                   (pos, getErrMsgTag msg, showWarningList [e])
           in  (asi_warnings aschedinfo) ++ (map processWarning warnings)
       new_aschedinfo = aschedinfo { asi_schedule = new_sched,
                                     asi_warnings = new_warnings }
   return (new_pkg, new_aschedinfo, methodDumpMap)


aDumpScheduleErr :: ErrorHandle -> Flags -> String -> APackage ->
                    AScheduleErrInfo -> IO ()
aDumpScheduleErr errh flags prefix pkg aschedinfo = do

   -- Extract fields from the package and schedinfo
   --
   let ifc = apkg_interface pkg
       rs = apkg_rules pkg

   let maybe_methodDumpMap =
           case (asei_v_sched_info aschedinfo) of
             Just vSchedInfo -> Just (genMethodDumpMap vSchedInfo ifc)
             _ -> Nothing
       rulePredMap  = [(rid, p) | (ARule { arule_id = rid,
                                           arule_pred = p }) <- rs ]

   -- Dump the schedule
   --
   when (showSchedule flags) $
       doShowSchedule errh flags prefix pkg (Left aschedinfo)
           maybe_methodDumpMap rulePredMap


doShowSchedule :: ErrorHandle -> Flags -> String -> APackage ->
                  Either AScheduleErrInfo AScheduleInfo ->
                  Maybe MethodDumpInfo -> [(ARuleId, APred)] -> IO ()
doShowSchedule errh flags prefix pkg
               aschedinfo maybe_methodDumpMap rulePredMap = do
    let
        maybe_schedule =
            case (aschedinfo) of
              Right r -> Just (asi_schedule r)
              Left l -> asei_schedule l

        maybe_order =
            case maybe_schedule of
              Just s -> Just (asch_rev_exec_order s)
              Nothing -> Nothing

        getRuleBlockers rid =
            case maybe_schedule of
              Just s -> let ruleBlockerMap =
                                concatMap ruleBlockers (asch_scheduler s)
                        in  case (lookup rid ruleBlockerMap) of
                              Nothing -> internalError("Unscheduled rules? " ++
                                                       ppReadable rulePredMap)
                              res -> res
              Nothing -> Nothing

    let ds = apkg_local_defs pkg

    let modstr = getIdBaseString (apkg_name pkg)
    let schedName :: String
        schedName  = mkSchedName (infoDir flags) prefix modstr
    --
    schedFileH <- openFileCatch errh emptyContext schedName WriteMode
    unless (quiet flags) $ putStrLn $ "Schedule dump file created: " ++
                                      (getRelativeFilePath schedName )
    let   outputHandles = schedFileH : [stdout | hasDump flags DFschedule]
    --
    --
    let schedPutStr :: String -> IO ()
        schedPutStr str = putStrHandles outputHandles str
    let schedPutStrLn :: String -> IO ()
        schedPutStrLn str = do schedPutStr str
                               mapM_ (`hPutChar` '\n') outputHandles
    let schedPutDoc :: Doc -> IO ()
        schedPutDoc d = schedPutStr (pretty 78 78 d)

    let topBanner = "=== Generated schedule for " ++ modstr ++ " ===\n"
    schedPutStrLn topBanner

    case (maybe_methodDumpMap) of
      Just methodDumpMap | ((not . null) methodDumpMap) -> do
          schedPutStrLn "Method schedule"
          schedPutStrLn "---------------"
          mapM_ (schedPutDoc . (dumpMethod flags True ds)) methodDumpMap
      _ -> return ()

    -- Dump rule schedule
    -- XXX should we sort, etc. to make this more efficient?
    let ruleDumpMap = [ (rid, p, blockers)
                            | (rid, p) <- rulePredMap,
                              let blockers = getRuleBlockers rid ]

    when ((not . null) ruleDumpMap) $ do
       schedPutStrLn "Rule schedule"
       schedPutStrLn "-------------"
       mapM_ (schedPutDoc . (dumpRule flags ds)) ruleDumpMap

    -- probably always non-null but might as well be safe
    case (maybe_order) of
      Just order | ((not . null) order) ->
        schedPutStr
            (pretty 78 78
                (text ("Logical execution order: ") <>
                (sepList (map (text . dropRulePrefix) (reverse order)) comma)))
      _ -> return ()

    schedPutStrLn ""
    schedPutStrLn (map (const '=') topBanner)
    -- Close the files
    mapM_ hFlush outputHandles
    mapM_ hClose (delete stdout outputHandles)


genMethodDumpMap :: VSchedInfo -> [AIFace] -> MethodDumpInfo
genMethodDumpMap vSchedInfo ifc = methodDumpMap
    where
           -- for now, we only report the conflict info
           -- XXX could include the rule-between info
           vMethConf = methodConflictInfo vSchedInfo

           -- don't include output clocks and resets
           -- don't include ready Ids
           methodList = filter (not . isRdyId) $
                        map aif_name (aIfaceMethods ifc)
           methodRdys = [(mn, p) | (AIDef { aif_name = mn, aif_value = (ADef _ _ p _) }) <- ifc, isRdyId mn]
           methodDumpMap =
             [ (mid, p, clist)
             | mid <- methodList
             , let p = fromMaybe aTrue (lookup (mkRdyId mid) methodRdys)
             , let clist = dumpOneLocal mid methodList
             ]
           dumpOneLocal = dumpOneConflicts setCF setSB setSBR
           setCF  = S.fromList (sCF vMethConf)
           setSB  = S.fromList (sSB vMethConf)
           setSBR = S.fromList (sSBR vMethConf)

dumpOneConflicts :: S.Set (AId, AId) -> S.Set (AId, AId) -> S.Set (AId, AId) ->
                    AId -> [AId] -> [(AId,RuleConflictType)]
dumpOneConflicts _ _ _ mid [] = []
dumpOneConflicts setCF setSB setSBR mid others = dumpConflicts mid others
    where  dumpConflicts :: AId -> [AId] -> [(AId,RuleConflictType)]
           dumpConflicts mid []          = []
           dumpConflicts mid (mid':rest) =
               case ((mid, mid') `S.member` setCF,
                     (mid', mid) `S.member` setCF,
                     (mid, mid') `S.member` setSB,
                     (mid', mid) `S.member` setSB,
                     (mid, mid') `S.member` setSBR,
                     (mid', mid) `S.member` setSBR
                    ) of
                 (True,_,_,_,_,_) ->
                     ((mid',ConflictFree)  : (dumpConflicts mid rest))
                 (_,True,_,_,_,_) ->
                     ((mid',ConflictFree)  : (dumpConflicts mid rest))
                 (False,False,True,False,False,False) ->
                     ((mid', SCBefore)     : (dumpConflicts mid rest))
                 (False,False,False,True,False,False) ->
                     ((mid', SCAfter)      : (dumpConflicts mid rest))
                 (False,False,True,True,False,False) ->
                     (if (mid == mid') then
                          (mid', SCBefore) -- method SC with itself
                      else
                          (mid', Complete)) -- alternate way of representing complete conflict
                     : (dumpConflicts mid rest)
                 (False,False,False,False,True,False) ->
                     ((mid', SCBeforeR)      : (dumpConflicts mid rest))
                 (False,False,False,False,False,True) ->
                     ((mid', SCAfterR)      : (dumpConflicts mid rest))
                 (False,False,False,False,True,True) ->
                     (if (mid == mid') then
                          (mid', SCBeforeR) -- method SC with itself
                      else
                          (mid', Complete)) -- alternate way of representing complete conflict
                     : (dumpConflicts mid rest)
                 (False,False,False,False,False,False) ->
                     ((mid', Complete)     : (dumpConflicts mid rest))
                 x@(a,b,c,d,e,f)  ->  internalError ("Unknown conflict type: " ++ ppReadable x
                                       ++ " " ++ (ppReadable mid) ++
                                       " " ++ (ppReadable mid') ++ "\n" ++
                                       "Sched sets: " ++ (ppReadable (setCF, setSB, setSBR)))


removeADefMethodPredsByRuleId :: [Id] -> [ADef] -> [ADef]
removeADefMethodPredsByRuleId [] ds = ds
removeADefMethodPredsByRuleId dropped_rule_ids ds =
    let
        dropped_id_set = S.fromList dropped_rule_ids

        isRuleProp (DefP_Rule {}) = True
        isRuleProp _              = False

        isForDroppedRule ps =
            case (find isRuleProp ps) of
              Just (DefP_Rule r) -> r `S.member` dropped_id_set
              _ -> internalError ("MethodPred with no DefP_Rule")

        dropDef (ADef i _ _ ps) =
            (hasIdProp i IdPMethodPredicate) &&
            (isForDroppedRule ps)
    in
        filter (not . dropDef) ds
