module AAddSchedAssumps(aAddSchedAssumps, aAddCFConditionWires) where

import CSyntax
import SymTab
import TypeCheck(topExpr)
import CType
import Type
import qualified TIMonad as TIM(runTI)
import Flags(Flags, showElabProgress)
import IConv(iConvExpr)
import ASyntax
import ASyntaxUtil
import ISyntax
import ISyntaxUtil hiding (noReset)
import IExpandUtils(HExpr, HeapData)
import IExpand(iExpand)
import ISplitIf(iSplitIf)
import AConv(aConv)
import ASchedule(extractCFPairsSP, errAction, RAT)
import AUses(MethodId(..), MethodUsers, UniqueUse(..), MethodUsesList, ucTrue,
             mergeUseMapData, extractCondition, ruleMethodUsesToUUs)
import AScheduleInfo(AScheduleInfo(..))
import VModInfo(VMethodConflictInfo, vSched)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import PreIds
import qualified Data.Map as M
import qualified Data.Set as S
import PPrint
import Pragma(ASchedulePragma)
import Error(internalError, ErrMsg(..), showErrorList, ErrorHandle)
import Id
import Position(noPosition)
import Util(unzipWith, ordPairBy, fst3)
import Util(mapSnd)

-- | Method name mapped to condition of usage
type MethodCondMap = M.Map AMethodId AExpr

-- | State elements to the map of method condition usage
type OMCondMap = M.Map AId (MethodCondMap)

-- | Rules to the objects whose methods they use (with conditions)
type RuleMethodMap = M.Map ARuleId (OMCondMap)

-- | We only need the method conflict info
type OSchedMap = M.Map AId VMethodConflictInfo

buildOMCondMap :: MethodUsesList -> OMCondMap
buildOMCondMap uses = M.fromListWith (M.unionWith aOr) omuses'
  where uses'   = mapSnd buildUseConditions uses
        omuses  = [(o, (m, c)) | (MethodId o m, c) <- uses' ]
        omuses' :: [(AId, MethodCondMap)]
        omuses' = mapSnd (uncurry M.singleton) omuses

buildUseConditions :: [UniqueUse] -> AExpr
buildUseConditions = aOrs . (map extractCondition)

uqWGet, uqWSet :: Id
uqWGet = unQualId idWGet
uqWSet = unQualId idWSet

-- We check for overlaps when updating the RAT in case we made a mistake while injecting the new wires.
newRatErr :: RAT -> RAT -> MethodId -> M.Map UniqueUse Integer -> M.Map UniqueUse Integer -> M.Map UniqueUse Integer
newRatErr oldRat newRatEntries m _ _ =
  internalError $ "Conflict between original RAT and newRatEntries on methodId " ++ ppReadable m ++ "\n" ++
                  "Should be impossible because newRatEntries is all about newly instantiated wires.\n" ++
                  "RAT:           " ++ ppReadable oldRat ++ "\n" ++
                  "newRatEntries: " ++ ppReadable newRatEntries

aAddSchedAssumps :: APackage -> ASchedule -> AScheduleInfo -> (APackage, AScheduleInfo)
aAddSchedAssumps apkg schedule schedinfo = (apkg'', schedinfo')
  where ruleMap :: M.Map ARuleId Integer
        ruleMap = M.fromList (zip (asch_rev_exec_order schedule) [0..])
        err i = internalError ("AAddAssumps - unknown rule: " ++ ppReadable i)
        get i = M.findWithDefault (err i) i ruleMap
        -- use reverse order because we want the last rule to come first
        -- since later rules will do the checking
        cmpRule r1 r2 = compare (get r1) (get r2)
        pragmas = apkg_schedule_pragmas apkg
        ruleMethodMap :: RuleMethodMap
        ruleMethodMap = M.map (buildOMCondMap .
                               ruleMethodUsesToUUs . snd)
                              (asi_rule_uses_map schedinfo)
        instSchedMap :: OSchedMap
        instSchedMap = M.fromList
                         [(n, methodConflictInfo (vSched vmi))
                             | AVInst { avi_vname = n, avi_vmi = vmi }  <- insts ]
        insts = apkg_state_instances apkg
        apkg' = apkg
        doCFAssumps = addCFAssumps pragmas ruleMethodMap instSchedMap cmpRule
        (rs', newUseInfos) = unzip (map doCFAssumps (apkg_rules apkg'))
        newUseInfo = concat newUseInfos
        apkg'' = apkg' { apkg_rules = rs' }
        newRatEntries = M.fromList $ map useInfoToRatEntry newUseInfo
        newUseMapEntries = map useInfoToUseMapEntry newUseInfo
        oldRat = asi_resource_alloc_table schedinfo
        newRat = M.unionWithKey (newRatErr oldRat newRatEntries) oldRat newRatEntries
        newUseMap = M.unionWith (mergeUseMapData)
                      (asi_method_uses_map schedinfo)
                      (M.fromListWith (mergeUseMapData) newUseMapEntries)
        schedinfo' = schedinfo { asi_method_uses_map = newUseMap,
                                 asi_resource_alloc_table = newRat }


addCFAssumps :: [ASchedulePragma] -> RuleMethodMap -> OSchedMap
             -> (ARuleId -> ARuleId -> Ordering) -> ARule
             -> (ARule, [(ARuleId, MethodId, UniqueUse)])
addCFAssumps pragmas ruleMethodMap instSchedMap cmpRule = proc_rule
  where cf_pairs = extractCFPairsSP pragmas
        sorted_cf_pairs = map (ordPairBy cmpRule) cf_pairs
        check_pairs = [ (a, [b]) | (a, b) <- sorted_cf_pairs ]
        check_map = M.fromListWith (++) check_pairs
        proc_rule r@(ARule { arule_id = rid }) =
          case (M.lookup rid check_map) of
            Nothing -> (r, [])
            Just rids ->
             let (new_assumps, useinfos) = unzip (mkCFAssumps ruleMethodMap instSchedMap rid rids)
             in (r { arule_assumps = arule_assumps r ++ new_assumps }, useinfos)

mkCFAssumps :: RuleMethodMap -> OSchedMap -> ARuleId -> [ARuleId]
            -> [(AAssumption, (ARuleId, MethodId, UniqueUse))]
mkCFAssumps ruleMethodMap instSchedMap rid rids = concatMap (mkCFAssump ruleMethodMap instSchedMap rid) rids

mkCFAssump :: RuleMethodMap -> OSchedMap -> ARuleId -> ARuleId
           -> [(AAssumption, (ARuleId, MethodId, UniqueUse))]
mkCFAssump ruleMethodMap instSchedMap r1 r2 = concat $ M.elems overlapMap
  where
    omcm_r1 = getOMCond r1
    omcm_r2 = getOMCond r2
    r1_s = getIdString r1
    r2_s = getIdString r2
    r2_WF = aBoolVar (mkIdWillFire r2)
    getOMCond r = case (M.lookup r ruleMethodMap) of
                    Nothing -> err r
                    Just m -> m
    err r = internalError ("AAddSchedAssumps: no OMCondMap: " ++ ppReadable r)
    overlapMap = M.intersectionWithKey checkMethodCalls omcm_r1 omcm_r2
    -- methods are ok if they appear in the CF list in either order
    -- or if they appear in the SB or SBR list in the correct execution order
    -- remember r2 executes before r1!
    -- r1 is the "second" rule, to which we attach scheduling logic
    isOKPair sched p@(m1, m2) = p `elem` sCF sched || p2 `elem` sCF sched ||
                                p2 `elem` sSB sched ||
                                p2 `elem` sSBR sched
       where p2 = (m2, m1)
    checkMethodCalls o methCondMap1 methCondMap2 = newAssumps
      where
        o_s = getIdString o
        sched = case (M.lookup o instSchedMap) of
                  Nothing -> internalError ("AddSchedAssumps: no VSchedInfo: " ++ ppReadable o)
                  Just sched -> sched
        -- convert to lists to do a cross-product
        newAssumps = [ (assump, useinfo) | (m1, c1) <- M.toList methCondMap1,
                                           (m2, _) <- M.toList methCondMap2,
                                           not (isOKPair sched (m1, m2)),
                                           let obj = mkCFCondWireInstId r2 o m2,
                                           -- extracts m2's condition from the wire
                                           -- include the WILL_FIRE because we don't check the tag bit
                                           let c2 = AMethCall aTBool obj uqWGet [],
                                           let c = aAnds [r2_WF, c1, c2],
                                           let m1_s = getIdString m1,
                                           let m2_s = getIdString m2,
                                           let cferr = (getPosition r1,
                                                        EConflictFreeRulesFail (r1_s, r2_s) o_s (m1_s, m2_s)),
                                           let str = showErrorList [cferr],
                                           let a = [errAction str],
                                           let assump = AAssumption c a,
                                           -- XXX ucTrue is conservative, but we don't use the UseCond anyway
                                           let useinfo = (r1, MethodId obj uqWGet, UUExpr c2 ucTrue)]

-- | Rule to the methods it uses (with conditions)
type RuleMethCondMap = M.Map ARuleId [(MethodId, AExpr)]

aAddCFConditionWires :: ErrorHandle -> SymTab -> M.Map AId HExpr -> Flags ->
                        APackage -> AScheduleInfo ->
                        IO (APackage, AScheduleInfo)
aAddCFConditionWires errh r alldefs flags apkg schedinfo =
   if (null cfPairs) then
    -- when tracing other stages, the unnecessary output from getRWireInstFn is
    -- annoying, so don't call it if not necessary
    return (apkg, schedinfo)
   else do
    rWireInstFn <- getRWireInstFn errh flags r alldefs
    let mkWireInst r (MethodId obj meth)= rWireInstFn (mkCFCondWireInstId r obj meth)
    let newWires = concatMap (buildWireInsts ruleMethodMap mkWireInst) (S.toList cfRules)
    return (apkg { apkg_rules = rules',
                   apkg_state_instances = oldState ++ newWires },
            schedinfo { asi_resource_alloc_table = newRat,
                        asi_method_uses_map = newUseMap })

  where pragmas = apkg_schedule_pragmas apkg
        cfPairs = extractCFPairsSP pragmas
        cfRules = S.fromList ((map fst cfPairs) ++ (map snd cfPairs))
        ruleMethodMap :: RuleMethCondMap
        ruleMethodMap = M.map (buildMethCondList .
                               ruleMethodUsesToUUs . snd)
                              (asi_rule_uses_map schedinfo)
        oldState = apkg_state_instances apkg
        (rules', newUseInfos) = unzipWith (addCFCondWires cfRules ruleMethodMap) (apkg_rules apkg)
        newUseInfo = concat newUseInfos
        newRatEntries = M.fromList $ map useInfoToRatEntry newUseInfo
        newUseMapEntries = map useInfoToUseMapEntry newUseInfo
        oldRat = asi_resource_alloc_table schedinfo
        newRat = M.unionWithKey (newRatErr oldRat newRatEntries) oldRat newRatEntries
        newUseMap = M.unionWith (mergeUseMapData)
                      (asi_method_uses_map schedinfo)
                      (M.fromListWith (mergeUseMapData) newUseMapEntries)

useInfoToRatEntry :: (ARuleId, MethodId, UniqueUse)
                  -> (MethodId, M.Map UniqueUse Integer)
useInfoToRatEntry (_,mid,u) = (mid, M.singleton u 1)

useInfoToUseMapEntry :: (ARuleId, MethodId, UniqueUse)
                     -> (MethodId, [(UniqueUse, MethodUsers)])
useInfoToUseMapEntry (rid, mid, u) = (mid, [(u, ([],[rid],[]))])

buildMethCondList :: MethodUsesList -> [(MethodId, AExpr)]
buildMethCondList uses = M.toList (M.fromListWith aOr uses')
  where uses'   = mapSnd buildUseConditions uses

-- | We need a function that will take an id and make us the RWire instance we want.
-- It's a little more complicated than you might expect
getRWireInstFn :: ErrorHandle -> Flags -> SymTab ->
                  M.Map AId HExpr -> IO (Id -> AVInst)
getRWireInstFn errh flags r alldefs = do
  let blobT = TAp tModule (TAp tVRWireN (cTNum 1 noPosition))
  case fst3 $ (TIM.runTI flags False r (topExpr blobT (CVar idVmkRWire1))) of
    Left errs -> internalError (ppReadable errs)
    Right (_,e') -> do
      let iexpr = iConvExpr errh flags r alldefs e'
      let def :: IDef HeapData
          def = IDef id_x (iGetType iexpr) iexpr []
      let flags' = flags { showElabProgress = False }
      iepkg <- iExpand errh flags' r alldefs False [] def
      rwire_pkg <- aConv errh [] flags (iSplitIf flags iepkg)
      case (apkg_state_instances rwire_pkg) of
        [rwire_inst] ->
          let params = take 1 (avi_iargs rwire_inst) ++ [nullClock, noReset]
              rwire_inst' = rwire_inst { avi_iargs = params }
          in return (\i -> rwire_inst' { avi_vname = i })
        is -> internalError ("getRWireBlob: " ++ ppReadable is)

-- | A clock that never ticks but is always ready
nullClock :: AExpr
nullClock = ASClock aTClock (AClock aFalse aTrue)

noReset :: AExpr
noReset = aNoReset

buildWireInsts :: RuleMethCondMap -> (ARuleId -> MethodId -> AVInst) -> ARuleId -> [AVInst]
buildWireInsts ruleMethCondMap mkWireInst r = map (mkWireInst r) methIds
  where methIds = case (M.lookup r ruleMethCondMap) of
                    Just ms -> map fst ms
                    Nothing -> internalError ("AAddSchedAssumps.buildWireInsts missing rule: " ++
                                             ppReadable r ++ ppReadable ruleMethCondMap)

-- | Add wire-setting actions and return new RAT entries
addCFCondWires :: S.Set ARuleId -> RuleMethCondMap -> ARule -> (ARule, [(ARuleId, MethodId, UniqueUse)])
addCFCondWires cfRules ruleMethCondMap r | rid `S.member` cfRules =
  case (M.lookup rid ruleMethCondMap) of
    Just ms ->
      let (newActions, newUseInfo) = unzip $ [(a, (rid, mid, UUAction a)) | (MethodId o m, c) <- ms,
                                                                            let obj = mkCFCondWireInstId rid o m,
                                                                            let mid = MethodId obj uqWSet,
                                                                            let a   = ACall obj uqWSet [aTrue,c]]
      in (r { arule_actions = arule_actions r ++ newActions }, newUseInfo)
    Nothing -> internalError ("AAddAchedAssumps.addCFCondWires missing rule: " ++
                              ppReadable r ++ ppReadable ruleMethCondMap)
  where rid = arule_id r
addCFCondWires cfRules ruleMethCondMap r = (r, [])
