{-# LANGUAGE PatternGuards #-}
-- AUses
--
-- This module is used by ASchedule to create a MethodUsesMap, which
-- is then used by RSchedule and exposed to later stages (AState)
-- through the output of the ASchedule stage.
--
-- MethodUsesMap relates MethodId to a list of UniqueUse (an expression
-- or action) and, for each use:
--   * a list of RuleId for rules which use the method in their condition,
--   * a list of RuleId for rules which use the method in their action,
--   * a list of AId for submodule instances which use the method in
--     their instantiation (e.g. continuous connection to an input port)
-- Thus, the data types MethodId, UniqueUse, MethodUsers, and RuleId are
-- also exported.
--
-- Other data types (notably RuleUsesMap)
-- are exposed for use by ASchedule and AAddSchedAssumps:
--
-- 1) ASchedule creates a list of Rules using its own "cvtARule" and "cvtIfc"
--    functions (which could probably be put here in AUses)
-- 2) Then it calls buildUseMaps to create get the use maps from AUses.
-- 3) buildUseMaps first builds a ruleUseMap (using ruleUsesMap)
-- 4) A complete uses map is created, with "createMethodUsesMap",
--    by inverting the RuleUsesMap and adding uses from the submodule
--    instances.
-- 5) Both maps are returned to ASchedule
-- 6) The ruleUseMap is used to check that rules have proper actions
--    (no parallel conflicting actions) using "verifySafeRuleActions"
--    (which could also be moved here).
-- 7) The ruleUseMap is also used by functions "cfConflicts" and "scConflicts"
--    to add conflict edges to the conflict graphs.  Again, this could be
--    abstracted so that ASchedule doesn't need knowledge of the internal
--    data structures.
-- 8) The MethodUsesMap is used by RSchedule for resource allocation.
--    (it is also used as part of clock-domain checking in the scheduler)
--
-- AAddSchedAssumps uses a RuleUsesMap because it needs to go from
-- rules to method calls to potentially conflicting method calls in
-- "conflict-free" rules

module AUses(
              MethodUsesMap, -- requires MethodId, UniqueUse, MethodUsers
              mergeUseMapData,
              MethodId(..), methodIdToId, getMIdPosition, getMIdObject,
              UniqueUse(..), UseCond(..), ucTrue,
              MethodUsesList,
              getUUPos, hasSideEffects, extractCondition, differentArgs,
              useDropCond,
              MethodUsers, -- requires RuleId
              RuleId,

              -- create the ruleUsesMap and methodUsesMap together
              buildUseMaps,

              -- used by ASchedule and AAddSchedAssumps
              RuleUsesMap,
              RuleUses(..),
              Rule(..), ruleName, rulePred, ruleAncestor,
              rumToObjectMap, rumToMethodUseMap,
              rumGetMethodIds, rumRuleUsesFF,
              getMethodActionUses, rumGetActionUses, lookupMethodActionUse,
              ruleMethodUsesToUUs
             ) where

import Eval
import ASyntax
import ASyntaxUtil
import qualified Data.Map as M
import qualified Data.Set as S
import Position
import Id
import FStringCompat
import Data.List(union, partition, foldl')
import Util
import PPrint
import PVPrint
import ErrorUtil(internalError)
import Prim
import IntLit
import Control.Monad(liftM, mapAndUnzipM)
import Control.Monad.State.Strict(State, runState, get, put)
-- import Debug.Trace


-- ==============================
-- Data Types: Rule and RuleId

-- RULE: internal rule/interface method rep for scheduler --
type RuleId = ARuleId
data Rule = Rule RuleId (Maybe RuleId) [APred] [AExpr] [AAction]
          -- name, source if split, predicates, non-predicate reads, writes

instance Eq Rule where
    (Rule rId _ _ _ _) == (Rule rId' _ _ _ _) = rId == rId' -- we can assume unique ids

instance PPrint Rule where
    pPrint d i (Rule rId _ rPred rReads rWrites) =
        sep $ map sep
                     [[text "rule:", pPrint d i rId], [text "pred:", pPrint d i rPred],
                      [text "reads:", pPrint d i rReads], [text "writes:", pPrint d i rWrites]]

ruleName :: Rule -> RuleId
ruleName (Rule rId _ _ _ _) = rId

ruleAncestor :: Rule -> Maybe RuleId
ruleAncestor (Rule _ ancestor _ _ _) = ancestor

rulePred :: Rule -> [APred]
rulePred (Rule _ _ rPred _ _) = rPred


-- ==============================
-- Data Types: MethodId

-- METHOD IDs: identifies the object and the method --
data MethodId = MethodId AId AMethodId deriving (Eq,Ord,Show) -- object.method
instance PPrint MethodId where
    pPrint d p mid = pPrint d p (methodIdToId mid)
instance PVPrint MethodId where
    pvPrint d p mid = pvPrint d p (methodIdToId mid)
instance NFData MethodId where
     rnf (MethodId o m) = rnf2 o m

methodIdToId :: MethodId -> Id
methodIdToId (MethodId id mid) = mkStId id mid

getMIdPosition :: MethodId -> Position
getMIdPosition (MethodId id mid) = getIdPosition id

-- return just the instance
-- (can be used, for instance, to see if two uses are on the same object)
getMIdObject :: MethodId -> AId
getMIdObject (MethodId i _) = i

-- ==============================
-- Data Types: UniqueUse

data UniqueUse = UUAction AAction
               | UUExpr AExpr UseCond
     deriving (Eq, Ord, Show)

instance PPrint UniqueUse where
    pPrint PDDebug _ u = text "<UniqueUse>" <+> pPrint PDReadable 0 u
    pPrint d i   (UUAction a) = pPrint d i a
    pPrint d i (UUExpr a c) | c == ucTrue = pPrint d i a
    pPrint d i u@(UUExpr a uc) = pPrint d i a <+>
                                           text "condition:" <+>
                                           pPrint d i (useCondToAExpr uc)

instance PPrintExpand UniqueUse where
    pPrintExpand ds d i (UUAction a) = pPrintExpand ds d i a
    pPrintExpand ds d i (UUExpr a _)   = pPrintExpand ds d i a

instance NFData UniqueUse where
    rnf (UUAction a) = rnf a
    rnf (UUExpr e c) = rnf2 e c

-- XXX why does this return True for actions?
-- XXX consider merging this and "hasSideEffects"
differentArgs :: UniqueUse -> UniqueUse -> Bool
differentArgs (UUExpr e1 c1) (UUExpr e2 c2) = e1 /= e2
differentArgs _ _ = True

hasSideEffects :: UniqueUse -> Bool
hasSideEffects (UUExpr _ _) = False
hasSideEffects _ = True

isUUAction :: UniqueUse -> Bool
isUUAction UUAction {} = True
isUUAction _ = False

getUUPos :: UniqueUse -> Position
getUUPos (UUAction act) = getIdPosition (aact_objid act)
getUUPos (UUExpr (AMethCall _ i _ _) _) = getIdPosition i
getUUPos (UUExpr _ _) = noPosition -- XXX internal error? get a real position?

extractCondition :: UniqueUse -> AExpr
extractCondition (UUAction act) | (c:_) <- aact_args act = c
extractCondition (UUAction act) = internalError("AUses - action without condition: "
                                                 ++ ppReadable act)
extractCondition (UUExpr _ uc) = useCondToAExpr uc

useCondToAExpr :: UseCond -> AExpr
useCondToAExpr uc = foldl aAnd aTrue exprs
  where true_list = S.toList (true_exprs uc)
        false_list = map aNot (S.toList (false_exprs uc))
        eq_list = map mkEq (M.toList (eq_map uc))
        mkEq  (e,i)  = APrim defaultAId aTBool PrimEQ [e, ASInt defaultAId (aType e) i]
        neq_list = concatMap mkNEq (M.toList (neq_map uc))
        mkNEq (e,is) = map (\i -> APrim defaultAId aTBool PrimBNot [mkEq (e,i)]) (S.toList is)
        exprs = true_list ++ false_list ++ eq_list ++ neq_list

useDropCond :: UniqueUse -> UniqueUse
useDropCond (UUExpr e c) = UUExpr e ucTrue
useDropCond a = a

-- ==============================
-- Data Types: ActionUses, ExprUses

-- map from a submodule to a map from methods (on the module) to their uses
type MethodExprUses = M.Map Id (M.Map Id (M.Map AExpr UseCond))
type MethodActionUses = M.Map Id (M.Map Id [AAction])

toListMethodExprUses :: MethodExprUses -> [(MethodId, [UniqueUse])]
toListMethodExprUses mus =
    [ (MethodId objId methId, map (\ (e,c) -> UUExpr e c) (M.toList uses))
          | (objId, methmap) <- M.toList mus,
            (methId, uses) <- M.toList methmap ]

toListMethodActionUses :: MethodActionUses -> [(MethodId, [UniqueUse])]
toListMethodActionUses mus =
    [ (MethodId objId methId, map UUAction uses)
          | (objId, methmap) <- M.toList mus,
            (methId, uses) <- M.toList methmap ]

-- ----------

type FFuncId = AId

-- map from a foreign function to its uses
type FFuncExprUses = M.Map FFuncId (M.Map AExpr UseCond)
type FFuncActionUses = M.Map FFuncId [AAction]

toListFFExprUses :: FFuncExprUses -> [(FFuncId, [UniqueUse])]
toListFFExprUses fus =
    [ (fId, map (\ (e,c) -> UUExpr e c) (M.toList uses))
          | (fId, uses) <- M.toList fus ]

toListFFActionUses :: FFuncActionUses -> [(FFuncId, [UniqueUse])]
toListFFActionUses fus =
    [ (fId, map UUAction uses)
          | (fId, uses) <- M.toList fus ]

-- ----------

type ExprUses = (MethodExprUses, FFuncExprUses)
type ActionUses = (MethodActionUses, FFuncActionUses)

noExprUses :: ExprUses
noExprUses = (M.empty, M.empty)

singleMethodExprUse :: AId -> AMethodId -> AExpr -> UseCond -> ExprUses
singleMethodExprUse i m e c =
    (M.singleton i (M.singleton m (M.singleton e c)),
     M.empty)

singleMethodActionUse :: AId -> AMethodId -> AAction -> ActionUses
singleMethodActionUse i m a =
    (M.singleton i (M.singleton m [a]),
     M.empty)

singleFFuncExprUse :: AId -> AExpr -> UseCond -> ExprUses
singleFFuncExprUse i e c = (M.empty, M.singleton i (M.singleton e c))

singleFFuncActionUse :: AId -> AAction -> ActionUses
singleFFuncActionUse i a = (M.empty, M.singleton i [a])

getMethodExprUses :: ExprUses -> MethodExprUses
getMethodExprUses = fst

getMethodActionUses :: ActionUses -> MethodActionUses
getMethodActionUses = fst

getFFuncExprUses :: ExprUses -> FFuncExprUses
getFFuncExprUses = snd

getFFuncActionUses :: ActionUses -> FFuncActionUses
getFFuncActionUses = snd

lookupMethodActionUse :: MethodId -> MethodActionUses -> Maybe [AAction]
lookupMethodActionUse (MethodId objId methId) objmap =
    case (M.lookup objId objmap) of
      Nothing -> Nothing
      Just methmap ->  M.lookup methId methmap

-- ----------

-- Merge expression uses by combining the use condition of identical exprs
-- (Ravi's comment: "merge only expressions -- merging actions is dangerous")

mergeExprUses :: [ExprUses] -> ExprUses
mergeExprUses uss =
  let
      mergeUsesFn :: M.Map AExpr UseCond -> M.Map AExpr UseCond ->
                     M.Map AExpr UseCond
      mergeUsesFn us1 us2 = M.unionWith orUseCond us1 us2

      mergeMethodUses :: [MethodExprUses] -> MethodExprUses
      mergeMethodUses ms = M.unionsWith (M.unionWith mergeUsesFn) ms

      mergeFFuncUses :: [FFuncExprUses] -> FFuncExprUses
      mergeFFuncUses fs = M.unionsWith mergeUsesFn fs

      (muss, fuss) = unzip uss
  in
      (mergeMethodUses muss, mergeFFuncUses fuss)

mergeActionUses :: [ActionUses] -> ActionUses
mergeActionUses uss =
  let
      mergeUsesFn = (++)

      mergeMethodUses :: [MethodActionUses] -> MethodActionUses
      mergeMethodUses ms = M.unionsWith (M.unionWith mergeUsesFn) ms

      mergeFFuncUses :: [FFuncActionUses] -> FFuncActionUses
      mergeFFuncUses fs = M.unionsWith mergeUsesFn fs

      (muss, fuss) = unzip uss
  in
      (mergeMethodUses muss, mergeFFuncUses fuss)

mergeExprUsesM :: [ExprUses] -> UCM (ExprUses)
mergeExprUsesM uss = do
  let
      mergeUsesFnM :: M.Map AExpr UseCond -> M.Map AExpr UseCond ->
                      UCM (M.Map AExpr UseCond)
      mergeUsesFnM us1 us2 = map_unionWithM orUseCondM us1 us2

      mergeMethodUsesM :: [MethodExprUses] -> UCM (MethodExprUses)
      mergeMethodUsesM ms = map_unionsWithM (map_unionWithM mergeUsesFnM) ms

      mergeFFuncUsesM :: [FFuncExprUses] -> UCM (FFuncExprUses)
      mergeFFuncUsesM fs = map_unionsWithM mergeUsesFnM fs

      (muss, fuss) = unzip uss
  merged_mus <- mergeMethodUsesM muss
  merged_fus <- mergeFFuncUsesM fuss
  return (merged_mus, merged_fus)

-- ----------

addUseCond :: DefMap -> AExpr -> ExprUses -> ExprUses
addUseCond dm c (mus, fus) =
    let
        addUC c' = andUseCond dm c c'
        isFalseCond c' = (c' == ucFalse)

        filterNullMethUses us =
            let us' = M.map (M.filter (not . M.null)) us
            in  M.filter (not . M.null) us'
        addCondMethUses us =
            let mapMethUses fn = M.map (M.map fn)
                dropFalse = M.filter (not . isFalseCond)
            in  filterNullMethUses (mapMethUses (dropFalse . M.map addUC) us)

        filterNullFFUses us = M.filter (not . M.null) us
        addCondFFUses us =
            let mapFFUses fn = M.map fn
                dropFalse = M.filter (not . isFalseCond)
            in  filterNullFFUses (mapFFUses (dropFalse . M.map addUC) us)

    in
        (addCondMethUses mus, addCondFFUses fus)

-- extract common uses with the same condition
-- only used in eDomain
intersectUses :: ExprUses -> ExprUses -> ExprUses
intersectUses (mus1, fus1) (mus2, fus2) = (mus', fus')
  where mus' = M.intersectionWith (M.intersectionWith M.intersection) mus1 mus2
        fus' = M.intersectionWith (M.intersection) fus1 fus2

-- return only uses unique to the first set
-- even if only the condition is different
-- only used in eDomain
minusUses :: ExprUses -> ExprUses -> ExprUses
minusUses (mus1, fus1) (mus2, fus2) = (mus', fus')
  where mus' = M.differenceWith mapmapdiff mus1 mus2
        fus' = M.differenceWith mapdiff fus1 fus2

        mapmapdiff s1 s2 = toMaybe (not (M.null s')) s'
          where s' = M.differenceWith mapdiff s1 s2
        mapdiff s1 s2 = toMaybe (not (M.null s')) s'
          where s' = s1 `M.difference` s2

-- ==============================
-- Data Types: RuleUses

-- predicate uses, action read uses, action write uses
-- note: actionvalue method calls will start out being mentioned in both
-- the action read and write uses, but we will filter out the read uses
data RuleUses = RuleUses ExprUses ExprUses ActionUses

instance PPrint RuleUses where
    pPrint d i (RuleUses pus rus wus) =
       let pmus = toListMethodExprUses $ getMethodExprUses pus
           rmus = toListMethodExprUses $ getMethodExprUses rus
           wmus = toListMethodActionUses $ getMethodActionUses wus
           pfus = toListFFExprUses $ getFFuncExprUses pus
           rfus = toListFFExprUses $ getFFuncExprUses rus
           wfus = toListFFActionUses $ getFFuncActionUses wus
       in  sep [
                sep [text "predicate reads (methods):", pPrint d i pmus],
                sep [text "action reads (methods):", pPrint d i rmus],
                sep [text "action writes (methods):", pPrint d i wmus],
                sep [text "predicate reads (funcs):", pPrint d i pfus],
                sep [text "action reads: (funcs)", pPrint d i rfus],
                sep [text "action writes: (funcs)", pPrint d i wfus]
               ]

instance Show RuleUses where
   show ruses = ppReadable ruses

-- AAddSchedAssumps uses the RuleUsesMap to generate the code to check
-- "conflict_free" assumptions.
-- XXX This function returns the old UniqueUses datatype, so that
-- XXX AAddSchedAssumps doesn't have to change, even though we've changed
-- XXX the internal representation.
ruleMethodUsesToUUs :: RuleUses -> MethodUsesList
ruleMethodUsesToUUs (RuleUses pus rus wus) =
    getMethodUUExprs pus ++
    getMethodUUExprs rus ++
    getMethodUUActions wus

-- ==============================
-- Data Types: RuleUsesMap

-- A map from rule names to the methods used in the rule.
-- This is paired with the rule's predicate to save the effort of a
-- separate lookup when computing the full condition for a method call
-- (the condition of the call AND'd with the rule's predicate).
type RuleUsesMap = M.Map RuleId (AExpr, RuleUses)

-- This is still around for ASchedule to idenitfy common Action uses
-- between two rules, for warning about arbitrary earliness.
-- XXX A more abstract entry point might be good?
rumGetActionUses :: RuleUsesMap -> ARuleId -> ActionUses
rumGetActionUses m r = case M.lookup r m of
              Just (_, RuleUses _ _ range) -> range
              _ -> errNotInUseMap r

-- The following are intended as more abstract entry points for ASchedule:

-- whether a rule uses foreign functions
rumRuleUsesFF :: RuleUsesMap -> ARuleId -> Bool
rumRuleUsesFF m r =
    case M.lookup r m of
      Just (_, RuleUses preds domain range) ->
          let eUsesFF = not . M.null . getFFuncExprUses
              aUsesFF = not . M.null . getFFuncActionUses
          in  eUsesFF preds || eUsesFF domain || aUsesFF range
      _ -> errNotInUseMap r

-- convert a RuleUseMap to a map from rule Id to the list of Ids of
-- submodules whose methods are used by the rule
rumToObjectMap :: RuleUsesMap -> M.Map ARuleId (S.Set Id)
rumToObjectMap m =
   let usesToObjIds (_, RuleUses preds domain range) =
           let eObjIds = M.keysSet . getMethodExprUses
               aObjIds = M.keysSet . getMethodActionUses
           in  S.unions [eObjIds preds, eObjIds domain, aObjIds range]
   in  M.map usesToObjIds m

-- convert a RuleUseMap to a map from rule Id to the methods that
-- the rule uses (grouped by submodule Id) mapped to their uses
rumToMethodUseMap :: RuleUsesMap ->
                     M.Map ARuleId (AExpr, M.Map Id (M.Map Id [UniqueUse]))
rumToMethodUseMap m =
    let usesToMethMap (pred, RuleUses preds domain range) =
            let toE (e, c) = UUExpr e c
                toA a = UUAction a
                convE = M.map (M.map (map toE . M.toList)) . getMethodExprUses
                convA = M.map (M.map (map toA)) . getMethodActionUses
            in  (pred, M.unionsWith (M.unionWith (++)) [convE preds, convE domain, convA range])
    in  M.map usesToMethMap m

-- a map from the submodules that a rule calls methods on
-- to the set of methods which are used
rumGetMethodIdMap :: RuleUsesMap -> ARuleId -> M.Map Id (S.Set Id)
rumGetMethodIdMap m r =
    case M.lookup r m of
      Just (_, RuleUses preds domain range) ->
          let convE us = M.map (M.keysSet) (getMethodExprUses us)
              convA us = M.map (M.keysSet) (getMethodActionUses us)
          in  M.unionsWith (S.union) [convE preds, convE domain, convA range]
      _ -> errNotInUseMap r

-- a list of all the submodule methods that a rule uses
-- (a flattened version of "rumGetMethodIdMap")
rumGetMethodIds :: RuleUsesMap -> ARuleId -> [MethodId]
rumGetMethodIds m r = [ MethodId objId methId
                        | (objId, methset) <- M.toList $ rumGetMethodIdMap m r,
                          methId <- S.toList methset ]

-- ==============================
-- Expr collection monad

-- This Use-Condition Monad (UCM) performs CSE on expression use conditions,
-- possibly creating new defs.  This is to address the "Ek bug" (1388) where
-- conditions that can be expressed with linear defs were instead being
-- expressed with expontential defs.

type DefMap = M.Map AId AExpr
type DefUseMap = M.Map AId ExprUses

-- condition under which an AExpr is used
-- since AExprs do not contain their condition (unlike AActions)

data UCState = UCState { nextNo :: !Int,
                         new_defs :: [ADef],
                         defMap :: DefMap,
                         defUseMap :: DefUseMap,
                         cseMap :: M.Map AExpr (AId, AType)
                       }

type UCM a = State (UCState) a

getDefMap :: UCM (DefMap)
getDefMap = liftM defMap get

getDefUses:: AId -> UCM (ExprUses)
getDefUses i = do
  um <- liftM defUseMap $ get
  case (M.lookup i um) of
    Just uses -> do
        -- traceM ("getDefUses hit:" ++ ppReadable i)
        return uses
    Nothing -> do
      -- traceM ("getDefUses miss: " ++ ppReadable (i, M.size um))
      dm <- getDefMap
      let err = errNoDef i
      let e = M.findWithDefault err i dm
      uses <- eDomain e
      s <- get
      let um' = M.insert i uses (defUseMap s)
      put (s { defUseMap = um' })
      -- traceM ("getDefUses: " ++ ppReadable (i, e, uses))
      return uses

initUCState :: [ADef] -> UCState
initUCState defs = UCState {
                     nextNo = 1,
                     new_defs = [],
                     -- is throwing away props incorrect?
                     cseMap = M.fromList [(e, (i,t)) | ADef i t e _props <- defs ],
                     defMap = M.fromList [(i, e) | ADef i _ e _props <- defs ],
                     defUseMap = M.empty
                   }

runUCState :: [ADef] -> UCM a -> (a, [ADef])
runUCState defs m = (res, new_defs s)
   where (res, s) = runState m (initUCState defs)

aUsesPref :: String
aUsesPref = "__duses"

getNextNo :: UCM (Int)
getNextNo = do
  s <- get
  let no = nextNo s
  put s { nextNo = no + 1 }
  return no

newDef :: AExpr -> UCM (AId, AType)
newDef e = do
  no <- getNextNo
  let pos = getPosition e
  let i = setBadId (mkId pos (mkFString (aUsesPref ++ (show no))))
  let t = aType e
  let def = ADef i t e [] -- props from somewhere? xxx
  s <- get
  let new_defs' = def : (new_defs s)
  let cseMap' = M.insert e (i,t) (cseMap s)
  put (s { new_defs = new_defs', cseMap = cseMap' })
  return (i, t)

getCseMap :: UCM (M.Map AExpr (AId, AType))
getCseMap = liftM cseMap $ get

cseWithArgs :: AExpr -> UCM (AExpr)
cseWithArgs e = do
  cseMap <- getCseMap
  case (M.lookup e cseMap) of
    Just (i, t) -> return (ASDef t i)
    Nothing -> do
      let args = ae_args e
      args' <- mapM cse args
      let e' = e { ae_args = args' }
      cseMap <- getCseMap
      case (M.lookup e' cseMap) of
        Just (i, t) -> return (ASDef t i)
        Nothing -> do (i, t) <- newDef e'
                      return (ASDef t i)

cse :: AExpr -> UCM (AExpr)
cse e@(APrim { }) = cseWithArgs e
cse e@(AMethCall { }) = cseWithArgs e
cse e@(ANoInlineFunCall { }) = cseWithArgs e
cse e@(AFunCall { }) = cseWithArgs e
cse e = return e

-- true expressions, false expressions, equality set, not-equality set
data UseCond = UseCond { true_exprs :: S.Set AExpr,
                         false_exprs :: S.Set AExpr,
                         eq_map :: M.Map AExpr IntLit,
                         neq_map :: M.Map AExpr (S.Set IntLit)
                       }
  deriving (Show, Eq, Ord)

instance NFData UseCond where
  rnf (UseCond t f eq neq) = rnf4 t f eq neq

instance NFData RuleUses where
    rnf (RuleUses pus rus wus) = rnf3 pus rus wus

ucTrue, ucFalse :: UseCond
ucTrue  = UseCond S.empty S.empty M.empty M.empty
ucFalse = UseCond (S.singleton (aFalse)) S.empty M.empty M.empty

{-
isTrueUseCond uc = S.null (true_exprs uc) &&
                   S.null (false_exprs uc) &&
                   M.null (eq_map uc) &&
                   M.null (neq_map uc)
-}

-- prepare for ORing two use conditions by capturing
-- overlapping AND terms and making a residual expression
preOrUseCond :: UseCond -> UseCond -> (UseCond, AExpr)
preOrUseCond uc1 uc2 =
    {-
    trace ("uc1: " ++ ppReadable (true_exprs uc1, false_exprs uc1,
                                  eq_map uc1, neq_map uc1)) $
    trace ("uc2: " ++ ppReadable (true_exprs uc2, false_exprs uc2,
                                  eq_map uc2, neq_map uc2)) $
    trace ("shared_uc: " ++ ppReadable (shared_true, shared_false,
                                        shared_eq, shared_neq)) $
    trace ("uc1_rest: " ++ ppReadable (true1, false1, eq1, neq1)) $
    trace ("uc2_rest: " ++ ppReadable (true2, false2, eq2, neq2)) $
    -}
    (shared_uc, or_expr)
  where shared_true  =
            S.intersection (true_exprs uc1) (true_exprs uc2)
        shared_false = S.intersection (false_exprs uc1) (false_exprs uc2)
        -- only keep eq_map entries if they equal the same value
        eq_match i1 i2 = toMaybe (i1 == i2) i1
        shared_eq = M.mapMaybe id $
                    (M.intersectionWith eq_match (eq_map uc1) (eq_map uc2))
        shared_neq = M.filter (not . S.null) $
                     (M.intersectionWith S.intersection) (neq_map uc1) (neq_map uc2)
        shared_uc = UseCond shared_true shared_false shared_eq shared_neq
        true1 = (true_exprs uc1) `S.difference` shared_true
        true2 = (true_exprs uc2) `S.difference` shared_true
        false1 = (false_exprs uc1) `S.difference` shared_false
        false2 = (false_exprs uc2) `S.difference` shared_false
        eq1 = (eq_map uc1) `M.difference` shared_eq
        eq2 = (eq_map uc2) `M.difference` shared_eq
        -- when neq expressions overlap,
        -- check if there are residual terms to preserve
        -- M.differenceWith keeps the original terms otherwise
        neq_diff s1 s2 = toMaybe (not (S.null base_result)) base_result
           where base_result = s1 `S.difference` s2
        neq1 = M.differenceWith neq_diff (neq_map uc1) shared_neq
        neq2 = M.differenceWith neq_diff (neq_map uc2) shared_neq
        uc1_rest = UseCond true1 false1 eq1 neq1
        uc2_rest = UseCond true2 false2 eq2 neq2
        or_expr = aOr (useCondToAExpr uc1_rest) (useCondToAExpr uc2_rest)

orUseCond :: UseCond -> UseCond -> UseCond
orUseCond  uc1 uc2 = if (isTrue or_expr) then uc else uc'
  where (uc, or_expr) = preOrUseCond uc1 uc2
        uc' = uc { true_exprs = S.insert or_expr (true_exprs uc) }

orUseCondM :: UseCond -> UseCond -> UCM UseCond
orUseCondM uc1 uc2 = do
  let (uc, or_expr) = preOrUseCond uc1 uc2
  if (isTrue or_expr) then
    return (uc)
   else do
    or_expr' <- cse or_expr
    let uc' = uc { true_exprs = S.insert or_expr' (true_exprs uc) }
    return uc'

-- Ravi's original comments:
--   we don't worry about expanding definitions here (even though the
--   resulting conditions become predicates in conflict-free assumptions)
--   because the only issue would be with port-limited resources that need
--   are converted to port references (everything else is rearranging of
--   known definitions and method calls)
--   port references are looked up by the full method call expression
--   (see AState.hs) and we don't change that
-- However, we do need to avoid inlining "noinline" function calls; so this
-- has been re-structured to back out the very last inlined def, if it
-- doesn't make progress.
--
andUseCond :: DefMap -> AExpr -> UseCond -> UseCond
andUseCond dm e c = andUseCond' dm Nothing e c

andUseCond' :: DefMap -> Maybe AExpr -> AExpr -> UseCond -> UseCond
andUseCond' dm _ d@(ASDef _ i) uc =
    andUseCond' dm (Just d) (M.findWithDefault err i dm) uc
  where err = internalError ("AUses.andUseCond - unknown def: " ++ ppReadable i)
andUseCond' dm _ (APrim _ _ PrimBNot [e]) uc = doBNot Nothing e
  where doBNot _ d@(ASDef _ i) = doBNot (Just d) (M.findWithDefault (err i) i dm)
        doBNot _ (APrim _ _ PrimEQ [x, ASInt _ _ i]) = doNEq x i uc
        doBNot (Just d) _ = addFalse d uc  -- don't inline the def
        doBNot Nothing e' = addFalse e' uc
        err i = internalError ("AUses.andUseCond - unknown def: " ++ ppReadable i)
andUseCond' dm _ eq@(APrim _ _ PrimEQ [x, ASInt _ _ i]) uc = doEQ x i uc
andUseCond' dm _ e uc | length es > 1 =
    {-# SCC "aucFold" #-} foldl' (flip (andUseCond' dm Nothing)) uc es
  where es = getAnds Nothing e
        getAnds _ (APrim _ _ PrimBAnd es') = concatMap (getAnds Nothing) es'
        getAnds _ d@(ASDef _ i) = getAnds (Just d) (M.findWithDefault (err i) i dm)
        getAnds (Just d) _ = [d]  -- don't inline the def
        getAnds Nothing e' = [e']
        err i = internalError ("AUses.andUseCond - unknown def: " ++ ppReadable i)
andUseCond' dm (Just d) _ uc = addTrue d uc  -- don't inline the def
andUseCond' dm Nothing e' uc = addTrue e' uc

doNEq :: AExpr -> IntLit -> UseCond -> UseCond
doNEq x i uc =
    case (M.lookup x (eq_map uc)) of
      Just j ->
          if (i == j) then ucFalse else uc
      Nothing ->
         let neq' = M.insertWith (S.union) x (S.singleton i) (neq_map uc)
         in uc { neq_map = neq' }

doEQ :: AExpr -> IntLit -> UseCond -> UseCond
doEQ x i uc =
  case (M.lookup x (eq_map uc)) of
    Just j -> if i == j then uc else ucFalse
    Nothing ->
      case (M.lookup x (neq_map uc)) of
        Just s ->
            if (i `S.member` s) then ucFalse
            else let eq' = M.insert x i (eq_map uc)
                     neq' = M.delete x (neq_map uc)
                 in uc { eq_map = eq', neq_map = neq' }
        Nothing -> let eq' = M.insert x i (eq_map uc)
                   in uc { eq_map = eq' }

addFalse :: AExpr -> UseCond -> UseCond
addFalse e uc
    | isFalse e                    = uc
    | e `S.member` (true_exprs uc) = ucFalse
    | isTrue e                     = ucFalse
    | otherwise                    = uc { false_exprs = S.insert e (false_exprs uc) }

addTrue :: AExpr -> UseCond -> UseCond
addTrue e uc
    | e `S.member` (false_exprs uc) = ucFalse
    | isFalse e                     = ucFalse
    | isTrue e                      = uc
    | otherwise                     = uc { true_exprs = S.insert e (true_exprs uc) }

-- ==============================
-- Function: Build the RuleUsesMap and use it to build the MethodUsesMap

buildUseMaps :: [ADef] -> [Rule] -> [AVInst] -> (RuleUsesMap, MethodUsesMap, [ADef])
buildUseMaps defs rules avis = (rum, mum, reverse new_defs)
  where ((rum, mum), new_defs) = runUCState defs m
        m = do rum <- ruleUsesMap rules
               -- traceM (ppReadable rum)
               mum <- createMethodUsesMap rum avis
               return (rum, mum)

ruleUsesMap :: [Rule] -> UCM RuleUsesMap
ruleUsesMap rules = liftM M.fromList (mapM f rules)
  where f r = do ru <- rUses r
                 let rp = aAnds (rulePred r)
                 return (ruleName r, (rp, ru))

rUses :: Rule -> UCM (RuleUses)
rUses (Rule _ _ preds reads writes) = do
  (wDomains, wRanges) <- mapAndUnzipM aUses writes

  -- could condition on the preds, but the users of this info
  -- already do that, so it is redundant
  rDomains <- mapM eDomain reads

  pDomains <- mapM eDomain preds
  ps <- mergeExprUsesM pDomains
  rs <- mergeExprUsesM (rDomains ++ wDomains)
  -- Action uses don't require monadic merging
  let ws = mergeActionUses wRanges
  return (RuleUses ps rs ws)

aUses :: AAction -> UCM (ExprUses, ActionUses)
aUses a@(ACall i mi (c:es)) = do
    cond_uses <- eDomain c
    dm <- getDefMap
    arg_uses  <- liftM (map (addUseCond dm c)) $ mapM eDomain es
    expr_uses <- mergeExprUsesM (cond_uses : arg_uses)
    let action_uses = singleMethodActionUse i (unQualId mi) a
    return (expr_uses, action_uses)

aUses a@(AFCall { aact_objid = i, aact_args = (c:es) }) = do
    cond_uses <- eDomain c
    dm <- getDefMap
    arg_uses  <- liftM (map (addUseCond dm c)) $ mapM eDomain es
    expr_uses <- mergeExprUsesM (cond_uses : arg_uses)
    let action_uses = singleFFuncActionUse i a
    return (expr_uses, action_uses)

aUses a@(ATaskAction { aact_objid = i, aact_args = (c:es) }) = do
    cond_uses <- eDomain c
    dm <- getDefMap
    arg_uses  <- liftM (map (addUseCond dm c)) $ mapM eDomain es
    expr_uses <- mergeExprUsesM (cond_uses : arg_uses)
    let action_uses = singleFFuncActionUse i a
    return (expr_uses, action_uses)

aUses a = internalError ("AUses - action without condition: " ++ ppReadable a)

eDomain :: AExpr -> UCM (ExprUses)
-- special cases for non-strict primitives
eDomain (APrim _ _ PrimIf [cnd, thn, els]) = do
  cond_uses <- eDomain cnd
  thn_uses  <- eDomain thn
  els_uses  <- eDomain els
  dm <- getDefMap
  let common_uses = thn_uses `intersectUses` els_uses
      thn_only    = addUseCond dm cnd (thn_uses `minusUses` els_uses)
      els_only    = addUseCond dm (aNot cnd) (els_uses `minusUses` thn_uses)
  mergeExprUsesM [cond_uses, common_uses, thn_only, els_only]
eDomain (APrim _ _ PrimBAnd [x, y]) = do
  x_uses <- eDomain x
  y_uses <- eDomain y
  dm <- getDefMap
  let common = x_uses `intersectUses` y_uses
      x_only = addUseCond dm y (x_uses `minusUses` y_uses)
      y_only = addUseCond dm x (y_uses `minusUses` x_uses)
  -- XXX Why is this not the monadic version "mergeExprUsesM"?
  -- XXX This could be a deliberate decision by Ravi to not CSE ANDed terms.
  -- XXX See, for instance, revision 14202.
  return (mergeExprUses [common, x_only, y_only])
eDomain (APrim _ _ PrimBOr [x, y]) = do
   x_uses <- eDomain x
   y_uses <- eDomain y
   dm <- getDefMap
   let common = x_uses `intersectUses` y_uses
       x_only = addUseCond dm (aNot y) (x_uses `minusUses` y_uses)
       y_only = addUseCond dm (aNot x) (y_uses `minusUses` x_uses)
   mergeExprUsesM [common, x_only, y_only]
eDomain (APrim _ _ PrimArrayDynSelect [arr_e, idx_e]) = do
   idx_uses <- eDomain idx_e
   arr_uses <- eDomainArray idx_e arr_e
   mergeExprUsesM [idx_uses, arr_uses]
eDomain (APrim { ae_args = es }) =
    -- should primitives have resource constraints?
    mapM eDomain es >>= mergeExprUsesM
eDomain e@(AMethCall _ i mi es) = do
    let this_use = singleMethodExprUse i (unQualId mi) e ucTrue
    es_uses <- mapM eDomain es
    mergeExprUsesM (this_use : es_uses)
eDomain e@(AFunCall { ae_objid = i, ae_args = es }) = do
    let this_use = singleFFuncExprUse i e ucTrue
    es_uses <- mapM eDomain es
    mergeExprUsesM (this_use : es_uses)
-- don't count noinline functions
eDomain e@(ANoInlineFunCall { ae_objid = i, ae_args = es }) =
    mapM eDomain es >>= mergeExprUsesM
-- don't count the return value uses of actionvalue, only the action part
eDomain (AMethValue { }) = return noExprUses
-- the uses are counted on the action side
eDomain (ATaskValue { }) = return noExprUses
eDomain e@(ASPort _ i) = return noExprUses
eDomain e@(ASParam _ i) = return noExprUses
eDomain (ASDef _ d) = getDefUses d
eDomain (ASInt _ _ _) = return noExprUses
eDomain (ASReal _ _ _) = return noExprUses
eDomain (ASStr _ _ _) = return noExprUses
eDomain (ASAny _ _) = return noExprUses
-- these are now expected, as eDomain is called on instantiation arguments
eDomain e@(ASClock { }) = return noExprUses
    --internalError ("AUses.eDomain unexpected clock" ++ ppReadable e)
eDomain e@(ASReset { }) = return noExprUses
    --internalError ("AUses.eDomain unexpected reset" ++ ppReadable e)
eDomain e@(ASInout { }) = return noExprUses
eDomain e@(AMGate { }) = return noExprUses

eDomainArray :: AExpr -> AExpr -> UCM (ExprUses)
{-
-- XXX PrimArrayDynSelect would have been pushed into the arms,
-- XXX so this shouldn't occur
eDomainArray idx_e (APrim _ _ PrimIf [cnd, thn, els]) = do
  cond_uses <- eDomain cnd
  thn_uses  <- eDomainArray idx_e thn
  els_uses  <- eDomainArray idx_e els
  dm <- getDefMap
  let common_uses = thn_uses `intersectUses` els_uses
      thn_only    = addUseCond dm cnd (thn_uses `minusUses` els_uses)
      els_only    = addUseCond dm (aNot cnd) (els_uses `minusUses` thn_uses)
  mergeExprUsesM [cond_uses, common_uses, thn_only, els_only]
-}
eDomainArray idx_e (APrim _ _ PrimBuildArray es) = do
  let max_idx = case (aType idx_e) of
                  ATBit sz -> (2^sz) - 1
                  _ -> internalError ("eDomainArray: idx_ty")
  -- XXX what about indexing out of range?
  -- XXX should the last element be considered the default
  let mkEq e n = APrim defaultAId aTBool PrimEQ [e, aNat n]
      mkUses (n, e) = do
        e_uses <- eDomain e
        dm <- getDefMap
        return $ addUseCond dm (mkEq idx_e n) e_uses
  -- only consider uses up to the maximum indexable element
  es_uses <- mapM mkUses (zip [0..max_idx] es)
  mergeExprUsesM es_uses
eDomainArray idx_e (ASDef _ i) = do
  -- XXX can we memoize results?
  dm <- getDefMap
  let arr_e' = M.findWithDefault (errNoDef i) i dm
  eDomainArray idx_e arr_e'
eDomainArray _ arr_e =
  internalError ("eDomainArray: unhandled: " ++ ppReadable arr_e)

-- ==============================
-- Data Types: MethodUsesMap

-- The users are:
-- * rules that use it in their predicate,
-- * rules that use it in their body (action), and
-- * submodule instantiations that use it in port connections.
type MethodUsers = ([RuleId], [RuleId], [AId])

-- XXX This could return an Either, instead of UniqueUse
type MethodUsesMap = M.Map MethodId [(UniqueUse, MethodUsers)]

type MethodUsesList = [(MethodId, [UniqueUse])]

mergeUseMapData :: [(UniqueUse, MethodUsers)] -> [(UniqueUse, MethodUsers)] -> [(UniqueUse, MethodUsers)]
mergeUseMapData a b | null exprBlobs   = actionMergeResult
                    | null actionBlobs = exprMergeResult
                    | otherwise = internalError("Method has both action and expr uses " ++ ppReadable blobs)
  where blobs = a ++ b
        (actionBlobs, exprBlobs) = partition (isUUAction . fst) blobs
        actionMergeResult = M.toList (M.fromListWith concatMethodUsers blobs)
        -- UUExpr merging needs to be handled carefully because we
        -- want to be able to look up uses without the use condition
        exprCondMerge (c1, u1) (c2, u2) = (orUseCond c1 c2, concatMethodUsers u1 u2)
        exprMergeList = [(e, (c, mus)) | (UUExpr e c, mus) <- blobs ]
        exprMergeMap  = M.fromListWith exprCondMerge exprMergeList
        exprMergeResult = [(UUExpr e c, mus) | (e, (c, mus)) <- M.toList exprMergeMap]


concatMethodUsers :: MethodUsers -> MethodUsers -> MethodUsers
concatMethodUsers (a,b,c) (d,e,f) = (a++d, b++e, c++f)

-- ==============================
-- Function: Create a MethodUsesMap
--     by inverting a RuleUsesMap and adding uses from submodule instance

getMethodUUExprs :: ExprUses -> [(MethodId, [UniqueUse])]
getMethodUUExprs = toListMethodExprUses . getMethodExprUses

getMethodUUActions :: ActionUses -> [(MethodId, [UniqueUse])]
getMethodUUActions = toListMethodActionUses . getMethodActionUses

createMethodUsesMap :: RuleUsesMap -> [AVInst] -> UCM (MethodUsesMap)
createMethodUsesMap rmap avis = do
  let methodUsesMap0 = invertRuleUsesMap rmap
  instUses <- aInstUseMap avis
  -- reverse the instance use-map
  let inst_edges = [(mId, [(uuse, ([], [], [instId])) | uuse <- us])
                         | (instId, uses) <- instUses,
                           -- uses for each method
                           (mId, us) <- getMethodUUExprs uses ]
  -- add the instance edges to the initial map (of just rule uses)
  -- add the edges to the initial map (of just rule uses)
      methodUsesMap =
          foldr (uncurry (M.insertWith (mergeWith muUnion))) methodUsesMap0 inst_edges
      -- function for merging the new edges
      -- XXX takes advantage of the new edges not having rule uses
      muUnion (_,_,zs) (xs',ys',zs') = (xs', ys', union zs zs')

  return (methodUsesMap)

-- convert (rule -> method -> uses) to (method -> uses -> users)
-- (list of instance users will be empty in the map)
invertRuleUsesMap :: RuleUsesMap -> MethodUsesMap
invertRuleUsesMap rMap =
    foldr (uncurry (M.insertWith mergeUseMapData)) M.empty $
    [cvt rId uses | (rId, (_, RuleUses pUses rUses wUses)) <- M.toList rMap,
                    let pMUses = getMethodUUExprs pUses,
                    let rMUses = getMethodUUExprs rUses,
                    let wMUses = getMethodUUActions wUses,
                    uses <- map Left pMUses ++ map Right (wMUses ++ rMUses)]
    where
        -- convert a Left/Right use into the proper triple form, for merging
        -- (Left for predicate uses, Right for action reads/writes)
        cvt rId (Left (mId, us)) =
            (mId, [(uUse, ([rId], [], [])) | uUse <- us])
        cvt rId (Right (mId, us)) =
            (mId, [(uUse, ([], [rId], [])) | uUse <- us])

-- create a mapping from an instance Id to the list of method call uses
-- in the instantiation of that submodule
-- (just returns the list form of the map, not a Map)
-- there is redundant computation here because we rebuild
-- the defUseMap and the defMap instead of reusing them
aInstUseMap :: [AVInst] -> UCM [(AId, ExprUses)]
aInstUseMap avis = mapM iUses avis
  where iUses avi = do
          arg_uses <- (mapM eDomain (avi_iargs avi) >>= mergeExprUsesM)
          return (avi_vname avi, arg_uses)

-- ==============================
-- Errors

errNotInUseMap :: ARuleId -> a
errNotInUseMap r =
    internalError $
        "AUses: inconsistent ATS (rule " ++ ppString r ++ " not in use map)"

errNoDef :: AId -> a
errNoDef d =
    internalError $
        "AUses: inconsistent ATS (no definition for " ++ ppString d ++ ")"

-- ==============================
