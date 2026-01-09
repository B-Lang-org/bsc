{-# LANGUAGE PatternGuards #-}
module LambdaCalcUtil(

    chkAPackage,
    lcAPackageProcess,

    getSubModArgs, getSubModType, getSubModAVMethReturnTypes,

    getAActionDefs,
    getAExprDefs,

    tsortActionsAndDefs, mergeStmts,

    MethodOrderMap, mkMethodOrderMap,

    AStmt(..), getCondExpr,

    DefMap, lookupDef,
    InstMap, lookupMod,

    mkATBool, mkATrue, mkAFalse

) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad(when)
import Control.Monad.State(State, runState, gets, get, put)
import Data.Maybe(isJust, catMaybes)
import Data.List(intercalate, partition, union, nub)

import Util(makePairs, flattenPairs, allSame, fst2of3)
import SCC(tsort)

import Error(internalError, EMsg, ErrMsg(..), ErrorHandle)
import Flags
import PPrint
import Id
import Position (getPosition)
import PreIds(idBool)
import IntLit
import Prim(PrimOp(..))
import VModInfo(vName, vArgs, vFields, vSched,
                VArgInfo(..), isClock, isReset, isInout,
                VFieldInfo(..),
                getVArgInfoName, getVNameString)
import SchedInfo
import ASyntax
import ASyntaxUtil(aMethCalls, aMethValues, aTaskValues, aSubst, mapAExprs, exprMap)
import AOpt(aOptAPackageLite)
import Params(isConstAExpr)

-- -------------------------

-- process the APackge before conversion
lcAPackageProcess :: ErrorHandle -> Flags -> APackage -> APackage
lcAPackageProcess errh flags apkg = (
  -- update the types of the primitives
  updateAPackageTypes
  .
  -- some optimzations
  aOptAPackageLite errh flags
  .
  -- inline ASAny suggestions
  -- (AExpand and AOpt assume that this has happened)
  inlineUndet
  .
  -- in exprs for method return values, lift actionvalue return value
  -- references to their own defs, so that the actionvalue can be
  -- properly sequenced
  makeMethodTemps
  ) apkg

-- -------------------------

-- XXX This duplicates code in "simExpandParams"
chkAPackage :: String -> APackage -> Maybe [EMsg]
chkAPackage dump_name apkg =
    let
        defs = apkg_local_defs apkg
        dmap = M.fromList [ (i, aSubst dmap e) | ADef i _ e _ <- defs ]
        port_ids = [ i | AAI_Port (i,_) <- apkg_inputs apkg ]

        inlineArg (Param {}, expr) = aSubst dmap expr
        inlineArg (Port {},  expr) = aSubst dmap expr
        inlineArg (_,        expr) = expr

        inlineArgs avi =
            let varginfo = vArgs (avi_vmi avi)
                es = avi_iargs avi
                es' = map inlineArg (zip varginfo es)
            in  avi { avi_iargs = es' }

        insts = apkg_state_instances apkg
        insts' = map inlineArgs insts
        --apkg' = apkg { apkg_state_instances = insts' }

        -- XXX We could check that the module does not have other
        -- XXX unsupported features; like clocks, resets, inouts
        wmsgs = concatMap (checkInstArgs dump_name port_ids) insts'
    in
        if (null wmsgs)
        then Nothing
        else Just wmsgs

checkInstArgs :: String -> [AId] -> AVInst -> [EMsg]
checkInstArgs dump_name port_ids avi =
    let
        inst_name = avi_vname avi
        iarg_pairs = getInstArgs avi
        -- drop clk/rst and only consider the other arguments
        iarg_pairs_no_clk =
            filter (\ (i,e) -> not (isClock i || isReset i) ) iarg_pairs
        -- separate Inout from normal ports/params
        (iarg_pairs_inout, iarg_pairs_port_or_param) =
            partition (\ (i,e) -> isInout i ) iarg_pairs_no_clk

        getIArgNames ia_pairs =
            map (getIdString . getVArgInfoName . fst) ia_pairs

        -- the dump does not support Inout, so create warnings
        inout_iarg_names = getIArgNames iarg_pairs_inout
        inout_iarg_warns =
            if (null iarg_pairs_inout)
            then []
            else [(getPosition inst_name,
                   EGeneric ("The " ++ dump_name ++ " dump does not support " ++
                             "Inout module arguments: " ++
                             intercalate ", " inout_iarg_names))]

        -- Bluesim does not support dynamic ports, so create errors
        dynamic_iarg_pairs =
            filter (not . isConstAExpr port_ids . snd) iarg_pairs_port_or_param
        -- the names of any ports with dynamic exprs
        dynamic_iarg_names = getIArgNames dynamic_iarg_pairs
        dynamic_iarg_warns =
            if (null dynamic_iarg_pairs)
            then []
            else [(getPosition inst_name,
                   EGeneric ("The " ++ dump_name ++ " dump does not support " ++
                             "dynamic module arguments: " ++
                             intercalate ", " dynamic_iarg_names))]
    in
        -- report as many at once
        inout_iarg_warns ++ dynamic_iarg_warns

-- -------------------------

type DefMap = M.Map Id ADef

lookupDef :: DefMap -> Id -> ADef
lookupDef defmap i =
    case (M.lookup i defmap) of
      Nothing -> internalError ("lookupDef: " ++ ppReadable i)
      Just res -> res

-- -------------------------

-- Digested AVInst info for each submodule instance
-- * The module name
-- * The numeric type arguments for polymorphic modules
-- * A map from AV method names to their return values
--
type InstMap = M.Map Id (String, [Integer], M.Map Id [AType])

lookupMod :: InstMap -> Id -> (String, [Integer], M.Map Id [AType])
lookupMod instmap obj =
    case (M.lookup obj instmap) of
      Nothing -> internalError ("lookupMod: " ++ ppReadable obj)
      Just m -> m

-- -------------------------

-- XXX This code is also in Bluesim (SimPackage, SimExpand, SimMakeCBlocks)
-- XXX Consider moving the code into ASyntaxUtil and sharing it

-- -----

-- map from submodule instance name to a set of pairs of method names
-- where the first method must execute before the second
-- (when executed sequentially for atomic execution in one action)
type MethodOrderMap = M.Map AId (S.Set (AId, AId))

mkMethodOrderMap :: [AVInst] -> MethodOrderMap
mkMethodOrderMap avis =
    let mkMethodOrderSet avi =
            S.fromList $ sSB (methodConflictInfo (vSched (avi_vmi avi)))
    in  M.fromList $ map (\avi -> (avi_vname avi, mkMethodOrderSet avi)) avis

findMethodOrderSet :: MethodOrderMap -> AId -> S.Set (AId, AId)
findMethodOrderSet mmap id =
    case M.lookup id mmap of
        Just mset -> mset
        Nothing -> internalError ("SimPackage.findMethodOrderSet: " ++
                                  "cannot find " ++ ppReadable id)

-- -----

-- Get all of the AIds used by AActions, as well as
-- the AIds used by the defs of those AIds, etc.
getAActionDefs :: DefMap -> M.Map AId (AType, AExpr) -> [AAction] ->
                  M.Map AId (AType, AExpr)
getAActionDefs def_map known [] = known
getAActionDefs def_map known (act:acts) =
  let known' = getAExprDefs def_map known (aact_args act)
  in  getAActionDefs def_map known' acts

-- Accumulate AIds used by an expression and its sub-expressions.
getAExprDefs :: DefMap -> M.Map AId (AType, AExpr) -> [AExpr] ->
                M.Map AId (AType, AExpr)
getAExprDefs _ known [] = known
getAExprDefs def_map known ((APrim _ _ _ args):es) =
  getAExprDefs def_map known (args ++ es)
getAExprDefs def_map known ((AMethCall _ _ _ args):es) =
  getAExprDefs def_map known (args ++ es)
getAExprDefs def_map known ((ANoInlineFunCall _ _ _ args):es) =
  getAExprDefs def_map known (args ++ es)
getAExprDefs def_map known ((AFunCall _ _ _ _ args):es) =
  getAExprDefs def_map known (args ++ es)
getAExprDefs def_map known ((ASDef _ i):es) =
  case (M.lookup i known) of
    Just _ -> getAExprDefs def_map known es
    Nothing ->
        case M.lookup i def_map of
          (Just def@(ADef _ t e _)) ->
              let known' = M.insert i (t, e) known
              in  getAExprDefs def_map known' ((adef_expr def):es)
          Nothing ->
              --getAExprDefs def_map known' es
              internalError ("getAExprDefs: def not found: " ++ ppReadable i)
getAExprDefs def_map known (_:es) = getAExprDefs def_map known es

-- -----

-- XXX The requires that method calls in value and actionvalue method return
-- XXX expressions have been lifted to temp defs, so that their execution can
-- XXX be sequenced properly (in case other methods have to be called after).
-- XXX See "makeMethodTemps".
--
tsortActionsAndDefs :: MethodOrderMap -> DefMap ->
                       M.Map AId (AType, AExpr) -> [AAction] ->
                       ([Either ADef AAction], M.Map (AId, AId) (AId, AType))
tsortActionsAndDefs mmap defmap uses acts =
    let
        -- we will create a graph where the edges are:
        -- * "Left AId" to represent a def (by it's name)
        -- * "Right Integer" to represent an action (by it's position in acts)

        -- The use of Left and Right was chosen to make Defs lower in
        -- the Ord order than Actions.  This way, tsort puts them first.

        -- ----------
        -- Defs

        -- find the defs
        used_defs :: [ADef]
        used_defs = map (\ (i, (t, e)) -> ADef i t e []) (M.toList uses)

        -- make edges for def-to-def dependencies
        def_edges =
            [ (Left i, map Left uses)
                  | ADef i _ e _ <- used_defs,
                    let uses = M.keys $ getAExprDefs defmap M.empty [e] ]

        -- ----------
        -- Actions

        -- give the actions a unique number and make a mapping
        -- (this is necessary because the same action can be repeated
        -- more than once ... for instance, $display on the same arguments)

        -- (numbering in order also helps the Ord order, for tsort)
        numbered_acts = zip [1..] acts
        act_map = M.fromList numbered_acts
        getAct n = case (M.lookup n act_map) of
                     Just d -> d
                     Nothing -> internalError "tsortActionsAndDefs: getAct"

        -- separate the sorts of actions
        -- * method calls we will re-order, respecting sequential composability
        -- * foreign task/function calls we will keep in order, but allow
        --   other things to come between them (because tasks can return
        --   values)

        isACall (_, ACall {}) = True
        isACall _ = False

        isATaskAction (_, ATaskAction {}) = True
        isATaskAction _ = False

        (method_calls, foreign_calls) = partition isACall numbered_acts
        task_calls = filter isATaskAction foreign_calls

        -- ----------
        -- foreign-to-foreign edges
        -- (to maintain the user-specified order of system/foreign-func calls)

        -- (are these still needed now that we use Ord to bias tsort?)
        foreign_edges =
            if (length foreign_calls > 1)
            then let mkEdge (n1,_) (n2,_) = (Right n2, [Right n1])
                 in  zipWith mkEdge (init foreign_calls) (tail foreign_calls)
            else []

        -- ----------
        -- Action to def edges

        -- any defs used by an action have to be computed before the
        -- action is called

        act_def_edges =
            [ (Right n, map Left uses)
                  | (n, a) <- numbered_acts,
                    let uses = M.keys $ getAActionDefs defmap M.empty [a] ]

        -- ----------
        -- Action method to Action method edges

        -- function to create order edges
        --    m1 `isBefore` m2 == True
        --       when (m1 SB m2) is in the VModInfo for the submodule
        isBefore (ACall obj1 meth1 _) (ACall obj2 meth2 _) =
            -- do they act on the same object?
            if (obj1 /= obj2)
            then False
            else let mset = findMethodOrderSet mmap obj1
                 in  (unQualId meth1, unQualId meth2) `S.member` mset
        isBefore _ _ = False

        -- order the method calls
        --   The edges must be of the form (a, as) s.t. all actions in "as"
        --   have to execute before "a".
        meth_edges = [ (Right n1, ns)
                          | (n1,a1) <- method_calls,
                            let ns = [ Right n2 | (n2,a2) <- numbered_acts,
                                                 a2 /= a1,
                                                 a2 `isBefore` a1 ] ]

        -- ----------
        -- ActionValue method edges

        (av_meth_edges, av_meth_local_vars) =
            mkAVMethEdges used_defs method_calls

        -- ----------
        -- ActionValue task edges

        -- Make edges from the task to the def that it sets
        -- (ATaskValue is always a top-level def, and the Id is stored
        -- in the ATaskAction by the ATaskSplice stage.)
        -- (Rather than remove the def for the ATaskValue and make edges from
        --  the users of that def to the ATaskAction, we leave the def in
        --  the graph and just generate nothing for it when we make statements
        --  from the flattened graph.)
        av_task_edges =
            [ (Left tmp_id, [Right n]) |
               (n, ATaskAction { ataskact_temp=(Just tmp_id) }) <- task_calls ]

        -- ----------
        -- Action / Value method call edges

        -- like isBefore, but for Action vs Value method
        isVMethSB v_obj v_meth (ACall a_obj a_meth _) =
            -- do they act on the same object?
            if (v_obj /= a_obj)
            then False
            else let mset = findMethodOrderSet mmap v_obj
                 in  (unQualId v_meth, unQualId a_meth) `S.member` mset
        isVMethSB _ _ _ = False

        isAMethSB v_obj v_meth (ACall a_obj a_meth _) =
            -- do they act on the same object?
            if (v_obj /= a_obj)
            then False
            else let mset = findMethodOrderSet mmap v_obj
                 in  (unQualId a_meth, unQualId v_meth) `S.member` mset
        isAMethSB _ _ _ = False

        -- value method calls which are SB with action methods
        -- need to be properly ordered
        --   Edges must be of the form (m1, m2) where the method "m2"
        --   has to be executed before "m1".
        mdef_edges =
            [ edge | ADef i _ e _ <- used_defs,
                     -- "aMethCalls" can return duplicates, but that's OK
                     (obj,meth) <- aMethCalls e,
                     edge <-
                           -- def SB act
                           [ (Right n, [Left i])
                               | (n,a) <- method_calls,
                                 isVMethSB obj meth a ] ++
                           -- act SB def (XXX can this happen?)
                           [ (Left i, map Right ns)
                               | let ns = map fst $
                                          filter ((isAMethSB obj meth) . snd)
                                              method_calls,
                                 not (null ns) ]
            ]

        -- ----------
        -- check the assumption that the arguments to the actions don't
        -- introduce ordering edges (that is, don't contain value method
        -- calls or values from AV methods or tasks)

        isBadActionArg e = not (null (aMethCalls e)) &&
                           not (null (aMethValues e)) &&
                           not (null (aTaskValues e))

        bad_acts = concatMap (filter isBadActionArg . aact_args) acts

        -- ----------
        -- put it together into one graph

        g =
{-
            trace ("acts = " ++ ppReadable numbered_acts) $
            trace ("foreign_edges = " ++ ppReadable (foreign_edges :: [Edge])) $
            trace ("av_task_edges = " ++ ppReadable av_task_edges) $
            trace ("av_meth_edges = " ++ ppReadable av_meth_edges) $
            trace ("meth_edges = " ++ ppReadable (meth_edges :: [Edge])) $
            trace ("mdef_edges = " ++ ppReadable mdef_edges) $
            trace ("act_def_edges = " ++ ppReadable (act_def_edges :: [Edge])) $
-}
            M.fromListWith union $ concat [ foreign_edges
                                          , av_task_edges
                                          , av_meth_edges
                                          , meth_edges
                                          , mdef_edges
                                          , act_def_edges
                                          , def_edges
                                          ]

        -- Convert the graph to the format expected by tsort.
        g_edges = M.toList g

    in
      if (not (null bad_acts))
      then internalError ("tsortActionsAndDefs: unexpected inlining:\n" ++ ppReadable bad_acts)
      else
        -- tsort returns Left if there is a loop, Right if sorted.
        -- (In the absence of restrictive edges, tsort uses Ord to put
        -- the lower valued nodes first.  Thus, we have chosen the node
        -- representation to put Defs first, followed by Actions in the
        -- order that they were give by the user.)
        case (tsort g_edges) of
            Left is -> internalError ("tsortActionsAndDefs: cyclic " ++
                                      ppReadable is)
            Right is ->
                let -- lookup def and action nodes
                    xs = map (either (Left . lookupDef defmap) (Right . getAct)) is
                in
                   (xs, av_meth_local_vars)

-- -----

type Node = Either AId Integer
type Edge = (Node, [Node])

-- -----

-- Given the defs and a list of only the action method calls (ACall),
-- returns:
-- * a list of edges between the defs using the value and any
--   ActionValue ACall which is producing the value
-- * a set of the ACall which are action value, mapped to the Id of the
--   def used to reference it and its type
mkAVMethEdges :: [ADef] -> [(Integer, AAction)] ->
                 ([Edge], M.Map (AId, AId) (AId, AType))
mkAVMethEdges ds method_calls =
    let
        -- check whether an AMethValue is from a particular action
        isMethValueOf v_obj v_meth (ACall a_obj a_meth _) =
            (v_obj == a_obj) && (v_meth == a_meth)
        isMethValueOf _ _ _ = False

        -- find the AMethValue references
        -- (assume that they are lifted to their own def)
        av_meth_refs = [ (i, obj, meth, ty)
                         | ADef i _ (AMethValue ty obj meth) _ <- ds ]

        -- the value reference from an ActionValue needs to come after
        -- the action method call.
        --   Edges must be of the form (i, as) where all actions in "as"
        --   have to execute before "i" is computed.
        av_meth_edges = [ (Left i, map Right ns)
                            | (i, obj, meth, _) <- av_meth_refs,
                              let ns = map fst $
                                       filter ((isMethValueOf obj meth) . snd)
                                           method_calls,
                              not (null ns) ]

        av_meths =
            let mkPair (i,o,m,t) = ((o,m),(i,t))
            in  M.fromList (map mkPair av_meth_refs)
    in
        (av_meth_edges, av_meths)

-- -----

-- XXX This was taken from SimExpand, but adjusted to also lift AMethValue
-- XXX and ATaskValue, and not to lift AFunCall.  If this is general,
-- XXX consider putting it in a common location, or consider always applying
-- XXX it to the ATS prior to this point.

makeMethodTemps :: APackage -> APackage
makeMethodTemps apkg =
  let (defs', iface') = cvt 1 (apkg_local_defs apkg) [] (apkg_interface apkg)
  in  apkg { apkg_local_defs = defs', apkg_interface = iface' }
  where
    cvt :: Integer -> [ADef] -> [AIFace] -> [AIFace] -> ([ADef], [AIFace])
    cvt _     defs iface [] = (defs, reverse iface)
    cvt seqNo defs iface (aif@(AIActionValue {}):aifs) =
        case (aif_value aif) of
          (ADef i ty e@(AMethCall {}) props) ->
              let (d, new_def) = makeTmp seqNo (aif_name aif) i ty e props
                  aif' = aif { aif_value = new_def }
              in  cvt (seqNo + 1) (d:defs) (aif':iface) aifs
          -- This is lifted for LC, which expects an id to bind to
          (ADef i ty e@(AMethValue {}) props) ->
              let (d, new_def) = makeTmp seqNo (aif_name aif) i ty e props
                  aif' = aif { aif_value = new_def }
              in  cvt (seqNo + 1) (d:defs) (aif':iface) aifs
          -- This is lifted for LC, which expects an id to bind to
          (ADef i ty e@(ATaskValue {}) props) ->
              let (d, new_def) = makeTmp seqNo (aif_name aif) i ty e props
                  new_i = adef_objid d
                  -- If task splicing has already occurred, then we need to
                  -- update the tmp ids in the task actions
                  new_body = map (updateRuleTaskTmp i new_i) (aif_body aif)
                  aif' = aif { aif_value = new_def, aif_body = new_body }
              in  cvt (seqNo + 1) (d:defs) (aif':iface) aifs
          _ -> cvt seqNo defs (aif:iface) aifs
    cvt seqNo defs iface (aif:aifs) = cvt seqNo defs (aif:iface) aifs

    makeTmp seqNo m mdef_id mdef_ty mdef_e mdef_props =
        let new_id = mkIdTempReturn True m seqNo
            new_mdef = (ADef mdef_id mdef_ty (ASDef mdef_ty new_id) mdef_props)
            new_d = (ADef new_id mdef_ty mdef_e mdef_props)
        in  (new_d, new_mdef)

    updateRuleTaskTmp old_d new_d r =
        let updateTaskTmp a@(ATaskAction {})
                | (ataskact_temp a == Just old_d)
                            = a { ataskact_temp = Just new_d }
            updateTaskTmp a = a
        in  r { arule_actions = map updateTaskTmp (arule_actions r) }

-- -------------------------

-- After the actions/defs are sorted, we want to further optimize the
-- code into if-else blocks.  For now, we just do a very simple merge
-- of adjacent actions with the same condition (and then with the inverse
-- condition).  When a def intervenes, we do not attempt to determine if
-- it can be included in the block and instead declare that the end of
-- the block.  There is also room for deeper analysis of the conditions
-- and for creating blocks inside blocks.

data AStmt = AStmtDef ADef
           -- the condition of the action has been removed from the arguments
           -- and represented as a set of AND terms
           | AStmtAction (S.Set AExpr) AAction
           -- the condition (as a set of AND terms) and the True and False arms
           | AStmtIf (S.Set AExpr) [AStmt] [AStmt]

instance PPrint AStmt where
  pPrint d p (AStmtDef def) =
      pparen (p > 0) (text "AStmtDef" <+> pPrint d 1 def)
  pPrint d p (AStmtAction cset act) =
      let c = getCondExpr cset
          as = aact_args act
          act' = act { aact_args = (c:as) }
      in  pparen (p > 0) (text "AStmtAction" <+> pPrint d 1 act')
  pPrint d p (AStmtIf cset tblk fblk) =
      pparen (p > 0)
          (text "AStmtIf" <+> pPrint d 1 (S.toList cset) <+>
           pPrint d 0 tblk <+> pPrint d 0 fblk)

getCondExpr :: S.Set AExpr -> AExpr
getCondExpr s = aBoolAnds (S.toList s)

mergeStmts :: DefMap -> [Either ADef AAction] -> [AStmt]
mergeStmts defmap stmts0 =
    let
        getStmtCond :: AStmt -> S.Set AExpr
        getStmtCond (AStmtIf c _ _) = c
        getStmtCond (AStmtAction c _) = c
        getStmtCond (AStmtDef _) = internalError ("getStmtCond")

        addStmtCond :: S.Set AExpr -> [AStmt] -> [AStmt]
        addStmtCond c [AStmtAction c0 a] = [AStmtAction (S.union c c0) a]
        addStmtCond c [AStmtIf c0 tblk []] = [AStmtIf (S.union c c0) tblk []]
        addStmtCond c blk = [AStmtIf c blk []]

        getAndTerms :: AExpr -> S.Set AExpr
        getAndTerms (APrim _ _ PrimBAnd as) = S.unions (map getAndTerms as)
        getAndTerms e | (isTrue e) = S.empty
        getAndTerms e | (isFalse e) =
            -- we'd need to represent the condition with a Maybe
            internalError ("getAndTerms: " ++ ppReadable e)
{- -- XXX This will inline defs, which can lead to unnecessary inlining and
   -- XXX to unused defs (which would need to be removed by a cleanup pass).
        getAndTerms e@(ASDef _ i) =
            -- if the def contains terms, then expand it;
            -- otherwise just return a single term of this def
            let e2 = adef_expr (lookupDef defmap i)
                e2_terms = getAndTerms e2
            in  -- if "e2_terms" is a singleton set containing "e2"
                if (S.member e2 e2_terms)
                then S.singleton e
                else e2_terms
-}
        getAndTerms e = S.singleton e

        -- if "C2 == C1 && REM", then return the remainder
        isSubset :: S.Set AExpr -> S.Set AExpr -> Maybe (S.Set AExpr)
        isSubset c1 c2 = if (S.null (S.difference c1 c2))
                         then Just (S.difference c2 c1)
                         else Nothing

        -- if "C2 == !C1 && REM", then return the remainder
        isInvSubset :: S.Set AExpr -> S.Set AExpr -> Maybe (S.Set AExpr)
        isInvSubset c1 c2 =
            -- XXX For a list of AND terms, we can only support a singleton C1
            if (S.size c1 == 1)
            then let inv_c1 = S.map aBoolNot c1
                 in  isSubset inv_c1 c2
            else Nothing

        -- whether an action can be merged with the previous statement,
        -- based on their conditions;
        -- if yes, returns the info for the merge (which branch and
        -- the remaining condition on the merged action)
        --
        -- We attempt to reconstruct the four following situations:
        --
        --    // c2 == (c1 && rem)
        --    if (c1) begin
        --       action1T;
        --       if (rem) action2;
        --    end
        --    else action1F;
        --
        --    // c1 == (c2 && rem)
        --    // XXX note that action1F is duplicated
        --    if (c2) begin
        --       if (rem) action1T else action1F;
        --       action2;
        --    end
        --    else action1F;
        --
        --    // c2 == (!c1 && rem)
        --    if (c1)
        --       action1T;
        --    else begin
        --       action1F;
        --       if (rem) action2;
        --    end
        --
        --    // c1 == (!c2 && rem)
        --    // XXX note that action1F is duplicated
        --    if (!c2) begin
        --       if (rem) action1T else action1F;
        --    else begin
        --       action1F;
        --       action2;
        --    end
        --
        -- The returned info is:
        -- * Whether the subset is as-is (not inverted) ("... == c && rem")
        -- * Whether "action2" has the remainder ("c2 == ... && rem"
        -- * The remainder
        --
        canMerge :: S.Set AExpr -> S.Set AExpr -> Bool ->
                    Maybe (Bool, Bool, S.Set AExpr)
        canMerge act_c prev_c _ | (S.null act_c) || (S.null prev_c) = Nothing
        -- the new action has a remainder (which might be True)
        canMerge act_c prev_c _
          -- c2 == (c1 && rem)
          | Just c_rem <- isSubset act_c prev_c = Just (True, True, c_rem)
          -- c2 == (!c1 && rem)
          | Just c_rem <- isInvSubset act_c prev_c = Just (False, True, c_rem)
        -- the previous stmt has a remainder
        -- XXX only do this merge when there is no "action1F" to duplicate
        canMerge act_c prev_c True
          -- c1 == (c2 && rem)
          | Just c_rem <- isSubset prev_c act_c = Just (True, False, c_rem)
          -- c1 == (!c2 && rem)
          | Just c_rem <- isInvSubset prev_c act_c = Just (False, False, c_rem)
        canMerge _ _ _ = Nothing

        -- Given the merge info, perform the merge of an action into
        -- the previous statement.  Blocks are constructed in reverse,
        -- to save the work of finding the last element when we merge
        -- the next action to this result.
        -- XXX consider using a "mkIf" function that optimizes BNot in the
        -- XXX condition?
        doMerge :: AStmt -> (S.Set AExpr, AAction) ->
                   (Bool, Bool, S.Set AExpr) -> AStmt
        doMerge (AStmtIf c1 tblk fblk) (_, a2) (True, True, c2_rem) =
            let -- recurse into the block and see if a merge is possible
                tblk' = addStmt tblk (AStmtAction c2_rem a2)
            in  (AStmtIf c1 tblk' fblk)
        doMerge (AStmtIf c1 tblk fblk) (_, a2) (False, True, c2_rem) =
            let -- recurse into the block and see if a merge is possible
                fblk' = addStmt fblk (AStmtAction c2_rem a2)
            in  (AStmtIf c1 tblk fblk')
        doMerge (AStmtIf _ tblk []) (c2, a2) (True, False, c1_rem) =
            let -- no recursive merge is needed
                tblk' = ((AStmtAction S.empty a2) : addStmtCond c1_rem tblk)
            in  (AStmtIf c2 tblk' [])
        doMerge (AStmtIf _ tblk []) (c2, a2) (False, False, c1_rem) =
            let -- no recursive merge is needed
                tblk' = addStmtCond c1_rem tblk
            in  -- rather than invert the condition, we swap the branches
                (AStmtIf c2 [AStmtAction S.empty a2] tblk')
        doMerge s1@(AStmtIf _ _ _) s2 inf =
            internalError ("doMerge: unexpected if: " ++ ppReadable (s1,s2,inf))
        -- XXX This is extra work (unnecessary recurse step),
        -- XXX but it's less error prone (only write one set of rules)
        doMerge (AStmtAction c1 a1) s2 inf =
            doMerge (AStmtIf c1 [AStmtAction S.empty a1] []) s2 inf
        doMerge (AStmtDef _) _ _ = internalError ("doMerge")

        -- Whether a statement has "else" Actions
        -- (which would need to be duplicated in some forms of merge)
        hasElseActions (AStmtIf _ _ []) = True
        hasElseActions _ = False

        -- Function for adding a new statement to an inverted set of
        -- previous statements, merging actions with common conditions
        -- when possible.
        addStmt :: [AStmt] -> AStmt -> [AStmt]
        addStmt ss s@(AStmtDef {}) = (s:ss)
        addStmt [] s@(AStmtAction {}) = [s]
        addStmt ss@((AStmtDef _):_) s@(AStmtAction {}) = (s:ss)
        addStmt (s1:ss) s2@(AStmtAction c2 a2) =
            case (canMerge c2 (getStmtCond s1) (hasElseActions s1)) of
              Nothing -> (s2:s1:ss)
              Just inf -> ((doMerge s1 (c2, a2) inf):ss)
        addStmt _ s = internalError ("addStmt: " ++ ppReadable s)

        -- after folding "addStmt" over the statements, we'll need to
        -- reverse all the blocks, with this function
        reverseStmts :: [AStmt] -> [AStmt]
        reverseStmts ss =
            let reverseStmt (AStmtIf c tblk fblk) =
                    (AStmtIf c (reverseStmts tblk) (reverseStmts fblk))
                reverseStmt s = s
            in  reverse (map reverseStmt ss)

        -- convert the Either into the initial (non-merged) statements
        -- XXX if "getAndTerms" does inlining here, then we loose the ability
        -- XXX to revert to the original def for actions that don't merge, etc
        makeStmt :: Either ADef AAction -> AStmt
        makeStmt (Left d) = AStmtDef d
        makeStmt (Right a) =
            case (aact_args a) of
              (c:as) -> AStmtAction (getAndTerms c) (a { aact_args = as })
              _ -> internalError ("makeStmt: aact_args: " ++ ppReadable a)
    in
        reverseStmts $ foldl addStmt [] $ map makeStmt stmts0

-- -------------------------

-- In BSC, the types of PrimIf and PrimBAnd etc use Bit#(1) instead of Bool.
-- We'd prefer not insert unnecessary conversions between Bit#(1) and Bool,
-- so we use the following ASyntax-to-ASyntax translation that changes
-- PrimIf, PrimBAnd, etc to operate on Bool; type inference is used to
-- the types of defs and literals, and type conversions are inserted only
-- when necessary.

-- XXX This code doesn't duplicate a def if it's used as both Bool and Bit#(1).
-- XXX Instead, the type is determined by the first use, and later uses have
-- XXX to convert if necessary.

-- XXX We could eliminate this transformation by having BSC primitives operate
-- XXX on Bool types natively.  Then, the ASyntax would also contain Bool types
-- XXX and the conversions necessary.  (See all the uses of "primOrd" and
-- XXX "primChr" in the Prelude.)

updateAPackageTypes :: APackage -> APackage
updateAPackageTypes apkg =
    let
        defmap = M.fromList [ (i, d) | d@(ADef i _ _ _) <- apkg_local_defs apkg ]

        updateFn = do
          rs <- mapM updateARuleTypes (apkg_rules apkg)
          ifcs <- mapM updateAIFaceTypes (apkg_interface apkg)
          avis <- mapM updateAVInstTypes (apkg_state_instances apkg)
          return (rs, ifcs, avis)

        ((rs', ifcs', avis'), defmap') = runUTM defmap updateFn
    in
        apkg { apkg_local_defs = M.elems defmap',
               apkg_rules = rs',
               apkg_interface = ifcs',
               apkg_state_instances = avis' }

-- -----

data UpdateTypesState =
    UpdateTypesState {
        -- read-only state
        ut_defMap :: DefMap,

        -- accumulated state
        ut_usedDefMap :: DefMap
    }

type UTM = State UpdateTypesState

runUTM :: DefMap -> (UTM a) -> (a, DefMap)
runUTM defmap fn =
    let state0 = UpdateTypesState { ut_defMap = defmap,
                                    ut_usedDefMap = M.empty }
        (v, state) = runState fn state0
    in  (v, ut_usedDefMap state)

addToUTMDefMap :: AId -> ADef -> UTM ()
addToUTMDefMap i d = do
  s <- get
  let dmap = ut_usedDefMap s
      dmap' = M.insert i d dmap
  put (s { ut_usedDefMap = dmap' })

-- -----

mkATBool, mkATBit1 :: AType
mkATBool = ATAbstract idBool []
mkATBit1 = ATBit 1

mkATrue, mkAFalse :: AExpr
mkATrue = aTrue { ae_type = mkATBool }
mkAFalse = aFalse { ae_type = mkATBool }

-- These functions exist in ASyntaxUtil, but they use the wrong type
-- (Bit1 vs Bool)

aBoolAnds :: [AExpr] -> AExpr
aBoolAnds [] = mkATrue
aBoolAnds [e] = e
aBoolAnds es =
    if any isFalse es
    then mkAFalse
    else aBoolAnds' (nub (filter (not . isTrue) es))
  where aBoolAnds' []  = mkATrue
        aBoolAnds' [e] = e
        aBoolAnds' es  = APrim defaultAId mkATBool PrimBAnd es

aBoolNot :: AExpr -> AExpr
aBoolNot (APrim defaultAId t PrimBNot [e]) = e
aBoolNot x | isTrue x   = aFalse
aBoolNot x | isFalse x  = aTrue
aBoolNot x              = APrim defaultAId mkATBool PrimBNot [x]

-- -----

updateAExprTypes_Bits :: AExpr -> UTM AExpr
updateAExprTypes_Bits e =
    updateAExprTypes (Just (getBitType e)) e >>= return . toBits
updateAExprTypes_BitsRealOrString :: AExpr -> UTM AExpr
updateAExprTypes_BitsRealOrString e =
    updateAExprTypes (Just (getBitRealOrStringType e)) e >>= return . toBitsRealOrString
updateAExprTypes_Bool :: AExpr -> UTM AExpr
updateAExprTypes_Bool e =
    updateAExprTypes (Just mkATBool) e >>= return . toBool

castBit1ToBool :: AExpr -> AExpr
castBit1ToBool e = APrim defaultAId mkATBool PrimChr [e]

castBoolToBit1 :: AExpr -> AExpr
castBoolToBit1 e = APrim defaultAId mkATBit1 PrimOrd [e]

castType :: Maybe AType -> AExpr -> AExpr
castType Nothing e = e
castType (Just exp_ty) e
    | (exp_ty == ae_type e) = e
    | (exp_ty == mkATBool) && (ae_type e == mkATBit1) = castBit1ToBool e
    | (exp_ty == mkATBit1) && (ae_type e == mkATBool) = castBoolToBit1 e
    -- it's OK to convert a sized string into an unsized string
    | (isUnsizedString exp_ty) && (isSizedString (ae_type e))
          = e { ae_type = exp_ty }
    | otherwise = internalError ("castType: " ++ ppReadable (exp_ty, ae_type e))

toBool :: AExpr -> AExpr
toBool = castType (Just mkATBool)

toBits :: AExpr -> AExpr
toBits e | (isBitType (ae_type e)) = e
toBits e | (isBoolType (ae_type e)) = castType (Just mkATBit1) e
toBits e = internalError ("toBits: unexpected conversion: " ++
                          ppReadable (ae_type e, e))

toBitsRealOrString :: AExpr -> AExpr
toBitsRealOrString e | (isBitType (ae_type e)) = e
toBitsRealOrString e | (isStringType (ae_type e)) = e
toBitsRealOrString e | (isBoolType (ae_type e)) = castType (Just mkATBit1) e
toBitsRealOrString e | (isRealType (ae_type e)) = e
toBitsRealOrString e =
  internalError ("toBitsRealOrString: unexpected conversion: " ++
                 ppReadable (ae_type e, e))

isBitType :: AType -> Bool
isBitType (ATBit _) = True
isBitType _ = False

isBoolType :: AType -> Bool
isBoolType t = (t == mkATBool)

isRealType :: AType -> Bool
isRealType (ATReal) = True
isRealType _ = False

getBitType :: AExpr -> AType
getBitType e =
    case (ae_type e) of
      t | isBitType t -> t
      t -> internalError ("getBitType: " ++ ppReadable t)

getBitRealOrStringType :: AExpr -> AType
getBitRealOrStringType e =
    case (ae_type e) of
      t | isBitType t -> t
      t | isStringType t -> t
      t | isRealType t -> t
      t -> internalError ("getBitType: " ++ ppReadable t)

-- -----

updateARuleTypes :: ARule -> UTM ARule
updateARuleTypes r = do
  -- rule predicate is Bool type
  p' <- updateAExprTypes_Bool (arule_pred r)
  as' <- mapM updateAActionTypes (arule_actions r)
  return (r { arule_pred = p',
              arule_actions = as' })

-- method predicate is Bool type, arguments and return values are Bit type;
-- except RDY methods which return Bool (to avoid unnecessary casting
-- backing and forth)
updateAIFaceTypes :: AIFace -> UTM AIFace
updateAIFaceTypes (AIDef mId args ws p (ADef i t e props) vfi assumps)
    | isRdyId i = do
  -- predicate should be constant True
  e' <- updateAExprTypes_Bool e
  return (AIDef mId args ws p (ADef i mkATBool e' props) vfi assumps)
updateAIFaceTypes (AIDef mId args ws p (ADef i t e props) vfi assumps) = do
  -- the predicate is either a RDY name or a constant, so we ignore it
  --p' <- updateAExprTypes_Bool p
  e' <- updateAExprTypes_Bits e
  return (AIDef mId args ws p (ADef i t e' props) vfi assumps)
updateAIFaceTypes (AIAction args ws p mId rs vfi) = do
  -- the predicate is either a RDY name or a constant, so we ignore it
  --p' <- updateAExprTypes_Bool p
  rs' <- mapM updateARuleTypes rs
  return (AIAction args ws p mId rs' vfi)
updateAIFaceTypes (AIActionValue args ws p mId rs (ADef i t e props) vfi) = do
  -- the predicate is either a RDY name or a constant, so we ignore it
  --p' <- updateAExprTypes_Bool p
  e' <- updateAExprTypes_Bits e
  rs' <- mapM updateARuleTypes rs
  return (AIActionValue args ws p mId rs' (ADef i t e' props) vfi)
updateAIFaceTypes e@(AIClock {}) = return e
updateAIFaceTypes e@(AIReset {}) = return e
updateAIFaceTypes e@(AIInout {}) = return e

updateAVInstTypes :: AVInst -> UTM AVInst
updateAVInstTypes avi = do
  -- instantiation arguments are Bit/Real/String type
  ias' <- mapM updateAExprTypes_BitsRealOrString (avi_iargs avi)
  return (avi { avi_iargs = ias' })

updateAActionTypes :: AAction -> UTM AAction
-- method condition is Bool type, arguments and return values are Bit type
updateAActionTypes (ACall obj meth (c:as)) = do
  c' <- updateAExprTypes_Bool c
  as' <- mapM updateAExprTypes_Bits as
  return (ACall obj meth (c':as'))
-- action task/ffunc condition is Bool type, arguments are Bit/Real/String type
updateAActionTypes (AFCall i f isC (c:as) isAssumpCheck) = do
  c' <- updateAExprTypes_Bool c
  as' <- mapM updateAExprTypes_BitsRealOrString as
  return (AFCall i f isC (c':as') isAssumpCheck)
-- actionvalue task/ffunc condition is Bool type,
-- arguments and return value are Bit/Real/String type
updateAActionTypes (ATaskAction i f isC k (c:as) tmp ret_t b) = do
  c' <- updateAExprTypes_Bool c
  as' <- mapM updateAExprTypes_BitsRealOrString as
  return (ATaskAction i f isC k (c':as') tmp ret_t b)
updateAActionTypes a = internalError ("updateAActionTypes: " ++ ppReadable a)

updateAExprTypes :: Maybe AType -> AExpr -> UTM AExpr
updateAExprTypes (Just exp_ty) (ASInt i t@(ATBit width) lit)
    | exp_ty == mkATBool = do
  when (width /= 1) $
      internalError ("updateAExprTypes: invalid Bool width: " ++ ppReadable width)
  -- XXX return a new type of literal, ASBool?
  return (ASInt i exp_ty lit)
updateAExprTypes _ e@(ASInt {}) = return e

updateAExprTypes _ e@(ASReal i t v) = return e
updateAExprTypes _ e@(ASStr i t v) = return e

updateAExprTypes mty (ASDef _ i) = do
  used_map <- gets ut_usedDefMap
  case (M.lookup i used_map) of
    Just (ADef { adef_type = def_ty }) -> return (ASDef def_ty i)
    Nothing -> do
      def_map <- gets ut_defMap
      case (M.lookup i def_map) of
        Nothing -> internalError ("updateAExprTypes: def: " ++ ppReadable i)
        Just (ADef { adef_expr = e, adef_props = props }) -> do
          e' <- updateAExprTypes mty e
          let t' = ae_type e'
          addToUTMDefMap i (ADef i t' e' props)  -- unsure whether properties should be propagated
          return (ASDef t' i)

-- ports/params are Bit type
updateAExprTypes _ e@(ASPort t i) = return e
updateAExprTypes _ e@(ASParam t i) = return e

-- if we know what value will be picked, update that
updateAExprTypes mty (ASAny i (Just e)) = do
  e' <- updateAExprTypes mty e
  return (ASAny i (Just e'))
updateAExprTypes _ e@(ASAny t Nothing) = return e

updateAExprTypes mty (APrim i t p args) = updateAPrimTypes mty p i t args

-- method arguments and return values are Bit type,
-- except RDY methods which return Bool
updateAExprTypes _ (AMethCall t obj meth as) = do
  as' <- mapM updateAExprTypes_Bits as
  let t' = if (isRdyId meth) then mkATBool else t
  return (AMethCall t' obj meth as')

-- method return values are Bit type
updateAExprTypes _ e@(AMethValue t obj meth) = return e

updateAExprTypes _ (ATupleSel _ _ _) = error "updateAExprTypes: multi-output methods not yet supported"
updateAExprTypes _ (ATuple _ _) = error "updateAExprTypes: multi-output methods not yet supported"

-- noinline function arguments and return values are Bit type
updateAExprTypes _ (ANoInlineFunCall t i f as) = do
  as' <- mapM updateAExprTypes_Bits as
  return (ANoInlineFunCall t i f as')

-- system and foreign function arguments and return values are Bit/Real/String type
updateAExprTypes _ (AFunCall t i f isC as) = do
  as' <- mapM updateAExprTypes_BitsRealOrString as
  return (AFunCall t i f isC as')

-- system and foreign task return values are Bit type
updateAExprTypes _ e@(ATaskValue t i f isC k) = return e

updateAExprTypes _ e@(ASClock {}) = return e
updateAExprTypes _ e@(ASReset {}) = return e
updateAExprTypes _ e@(ASInout {}) = return e

-- XXX allow a gate to be Bool?
updateAExprTypes _ e@(AMGate t o c) = return e


updateAPrimTypes :: Maybe AType -> PrimOp -> AId -> AType -> [AExpr] -> UTM AExpr
updateAPrimTypes mty PrimIf i t [ec, et, ef] = do
  -- force "c" to be Bool
  new_ec <- updateAExprTypes_Bool ec
  et0 <- updateAExprTypes mty et
  ef0 <- updateAExprTypes mty ef
  -- if the types of the arms don't match, force them to the expected type
  (new_et, new_ef) <-
      if (ae_type et0 == ae_type ef0)
      then return (et0, ef0)
      else let et1 = castType mty et0
               -- feed in the type of et1, in case mty is Nothing,
               -- so that at least both arms match
               ef1 = castType (Just (ae_type et1)) ef0
           in  return (et1, ef1)
  return (APrim i (ae_type new_et) PrimIf [new_ec, new_et, new_ef])
updateAPrimTypes mty PrimIf i t as =
  internalError ("updateAPrimTypes: PrimIf: wrong number of args: " ++
                 ppReadable as)

updateAPrimTypes mty PrimCase i t (idx:dflt:ces) = do
  -- force "idx" to be Bits
  new_idx <- updateAExprTypes_Bits idx
  let (cs, es) = unzip (makePairs ces)
  -- force the conditions to be Bits
  new_cs <- mapM updateAExprTypes_Bits cs
  -- convert the arms
  new0_es <- mapM (updateAExprTypes mty) es
  -- make sure that all the arms and default have the same type
  (new_dflt, new_es, new_t) <-
      -- do all of the types of the arms match?
      if (allSame (map ae_type new0_es))
      then do -- make sure the default has the same type
              let mty_arms =
                      case new0_es of
                        (e:_) -> Just (ae_type e)
                        _ -> mty  -- no arms? use the expected type
              new_dflt <- updateAExprTypes mty_arms dflt
                              >>= return . castType mty_arms
              let new_t = ae_type new_dflt
              return (new_dflt, new0_es, new_t)
      else do -- force them all to the expected type
              -- (if no expected type, use the first type)
              let mty_arms =
                      if (isJust mty)
                      then mty
                      else case new0_es of
                             (e:_) -> Just (ae_type e)
                             _ -> -- can't be no arms if they differ!
                                  internalError ("updateAPrimTypes: case")
              let new_es = map (castType mty_arms) new0_es
              new_dflt <- updateAExprTypes mty_arms dflt
                              >>= return . castType mty_arms
              let new_t = ae_type new_dflt
              return (new_dflt, new_es, new_t)
  -- put it all together
  let new_ces = flattenPairs (zip new_cs new_es)
  return (APrim i new_t PrimCase (new_idx:new_dflt:new_ces))
updateAPrimTypes mty PrimCase i t as =
  internalError ("updateAPrimTypes: PrimCase: wrong number of args: " ++
                 ppReadable as)

updateAPrimTypes mty PrimArrayDynSelect i t [arr, idx] = do
  -- force "idx" to be Bits
  new_idx <- updateAExprTypes_Bits idx
  -- pass the expected type to the array
  -- XXX the size of the array in "arr_mty" is not used
  let arr_mty = case mty of
                  Nothing -> Nothing
                  Just t -> Just (ATArray 0 t)
  new_arr <- updateAExprTypes arr_mty arr
  let new_t = case (ae_type new_arr) of
             ATArray _ t -> t
             _ -> internalError ("updateAPrimTypes: PrimArrayDynSelect: " ++
                                 "unexpected array type: " ++ ppReadable new_arr)
  return (APrim i new_t PrimArrayDynSelect [new_arr, new_idx])
updateAPrimTypes mty PrimArrayDynSelect i t as =
  internalError ("updateAPrimTypes: PrimArrayDynSelect: wrong number of args: "
                 ++ ppReadable as)

updateAPrimTypes arr_mty PrimBuildArray i t as = do
  let mty = case arr_mty of
              Nothing -> Nothing
              Just (ATArray _ t) -> Just t
              Just _ -> internalError ("updateAPrimTypes: PrimBuildArray: " ++
                                       "invalid expected type: " ++
                                       ppReadable arr_mty)
  new0_as <- mapM (updateAExprTypes mty) as
  -- force all the elements to be the same
  let fst_elem_t =
          case new0_as of
            (e:_) -> ae_type e
            _ -> internalError ("updateAPrimTypes: PrimBuildArray: size zero")
  let (new_as, new_elem_t) =
          if (allSame (map ae_type new0_as))
          then (new0_as, fst_elem_t)
          else -- force them all to the expected type
               -- (if no expected type, use the first type)
               let new_elem_t = case mty of
                                  Just t -> t
                                  Nothing -> fst_elem_t
                   new_as = map (castType (Just new_elem_t)) new0_as
               in  (new_as, new_elem_t)
  let new_t = case t of
                ATArray sz _ -> ATArray sz new_elem_t
                _ -> internalError ("updateAPrimTypes: PrimBuildArray: " ++
                                    "invalid prim type: " ++ ppReadable t)
  return (APrim i new_t PrimBuildArray new_as)

-- Arguments must be the same type, result is Bool
updateAPrimTypes _ PrimEQ i t [arg1, arg2] = do
  -- force the arms to be of the same type
  arg1' <- updateAExprTypes Nothing arg1
  let arg1'_type = ae_type arg1'
  arg2' <- updateAExprTypes (Just arg1'_type) arg2
             >>= return . castType (Just arg1'_type)
  return (APrim i mkATBool PrimEQ [arg1', arg2'])
updateAPrimTypes _ PrimEQ i t as =
  internalError ("updateAPrimTypes: PrimEQ: wrong number of args: " ++
                 ppReadable as)

-- Bool arguments, Bool result
updateAPrimTypes _ PrimBOr  i t args = updateAPrim_BoolBool i t PrimBOr args
updateAPrimTypes _ PrimBAnd i t args = updateAPrim_BoolBool i t PrimBAnd args
updateAPrimTypes _ PrimBNot i t args = updateAPrim_BoolBool i t PrimBNot args

-- Bit arguments, Bool result
updateAPrimTypes _ PrimULE i t args = updateAPrim_BitsBool i t PrimULE args
updateAPrimTypes _ PrimULT i t args = updateAPrim_BitsBool i t PrimULT args
updateAPrimTypes _ PrimSLE i t args = updateAPrim_BitsBool i t PrimSLE args
updateAPrimTypes _ PrimSLT i t args = updateAPrim_BitsBool i t PrimSLT args

-- Everything else is Bit arguments, Bit result
-- XXX consider updating the sizes to arithmetic operations?
updateAPrimTypes _ p i t args = updateAPrim_BitsBits i t p args

updateAPrim_BoolBool :: AId -> AType -> PrimOp -> [AExpr] -> UTM AExpr
updateAPrim_BoolBool i _ p as = do
  as' <- mapM updateAExprTypes_Bool as
  return (APrim i mkATBool p as')

updateAPrim_BitsBool :: AId -> AType -> PrimOp -> [AExpr] -> UTM AExpr
updateAPrim_BitsBool i _ p as = do
  as' <- mapM updateAExprTypes_Bits as
  return (APrim i mkATBool p as')

updateAPrim_BitsBits :: AId -> AType -> PrimOp -> [AExpr] -> UTM AExpr
updateAPrim_BitsBits i t p as = do
  as' <- mapM updateAExprTypes_Bits as
  return (APrim i t p as')

-- -------------------------

-- This is a lite version of "aDropUndet" (since we don't want to replace
-- all ASAny, just those with suggested values)

inlineUndet :: APackage -> APackage
inlineUndet = mapAExprs g
  where
    g = exprMap f

    f (ASAny _ (Just e)) = Just (g e)
    f _                  = Nothing

-- -------------------------

getSubModAVMethReturnTypes :: AVInst -> M.Map Id [AType]
getSubModAVMethReturnTypes avi =
    let
        meth_types = avi_meth_types avi
        vfis = vFields (avi_vmi avi)

        mkPair vfi (_, Just _, ret_tys) = Just (vf_name vfi, ret_tys)
        mkPair _ _ = Nothing

        pairs = catMaybes $ zipWith mkPair vfis meth_types
    in
        M.fromList pairs

-- -------------------------

-- This table is similar to the one in SimPrimitiveModules:
-- Some primitive modules are polymorphic; this is implemented in Verilog
-- using a parameter argument, but in Bluesim/LambdaCalculus we need the
-- templating to be part of the module type.  So this function extracts
-- the type arguments from the AVInst.

-- For now, we assume that the types are numeric
getSubModType :: AVInst -> (String, [Integer])
getSubModType avi = fst2of3 $ getSubModArgs avi

getSubModArgs :: AVInst -> (String, [Integer], [AExpr])
getSubModArgs avi =
    let mod = getVNameString (vName (avi_vmi avi))
        args = map snd $ filter (\ (i, e) -> not (isClock i || isReset i))
                                (getInstArgs avi)
    in  case (M.lookup mod primMap) of
          Nothing ->
              -- synthesized user modules are not polymorphic
              -- (all the args are real args, not type parameters)
              (mod, [], args)
          Just argFn ->
              let (ts, es) = argFn mod args
              in  (mod, ts, es)

primMap :: M.Map String (String -> [AExpr] -> ([Integer], [AExpr]))
primMap =
  M.fromList $
    [ ("RegN",               sizedType)
    , ("RegUN",              sizedType)
    , ("RegA",               sizedType)
    , ("CRegN5",             sizedType)
    , ("CRegUN5",            sizedType)
    , ("CRegA5",             sizedType)
    , ("CrossingBypassWire", sizedType)
    , ("CrossingRegN",       sizedType)
    , ("CrossingRegUN",      sizedType)
    , ("CrossingRegA",       sizedType)
    , ("RevertReg",          sizedType)
    , ("ConfigRegN",         sizedType)
    , ("ConfigRegUN",        sizedType)
    , ("ConfigRegA",         sizedType)
    , ("RWire",              sizedType)
    , ("BypassWire",         sizedType)
    , ("FIFO1",              sizedType)
    , ("FIFO2",              sizedType)
    , ("SizedFIFO",          sizedType)
    , ("FIFOL1",             sizedType)
    , ("FIFOL2",             sizedType)
    , ("SizedFIFOL",         sizedType)
    , ("RegFile",            memType)
    , ("RegFileLoad",        memFileType)
    , ("BRAM1",              bramType)
    , ("BRAM1Load",          bramFileType)
    , ("BRAM1BE",            bramEnsType)
    , ("BRAM1BELoad",        bramFileEnsType)
    , ("BRAM2",              bramType)
    , ("BRAM2Load",          bramFileType)
    , ("BRAM2BE",            bramEnsType)
    , ("BRAM2BELoad",        bramFileEnsType)
    , ("Probe",              sizedType)
    , ("ProbeWire",          sizedType)
    , ("Counter",            sizedType)
    , ("RegTwoN",            sizedType)
    , ("RegTwoUN",           sizedType)
    , ("RegTwoA",            sizedType)
    -- These are multiclock, so we don't support them anyway,
    -- but included for completeness
    , ("RegAligned",         sizedType)
    , ("SyncRegister",       sizedType)
    , ("SyncFIFO",           sizedType)
    , ("SyncFIFO1",          sizedType)
    , ("SyncFIFOLevel",      sizedType)
    , ("BypassCrossingWire", sizedType)
    , ("DualPortRam",        memType)
    , ("LatchCrossingReg",   sizedType)
    ]
  where
    mkErr :: String -> String -> [AExpr] -> String
    mkErr mod desc args =
        let msg = (text "Expected module") <+> (text mod) <+>
                  (text "to have") <+> (text desc) <+>
                  (text "but it was given arguments: ") <+>
                  (pPrint PDReadable 0 args)
        in render msg

    sizedType :: String -> [AExpr] -> ([Integer], [AExpr])
    sizedType _ ((ASInt _ _ sz):es) = ([ilValue sz], es)
    sizedType mod args =
        internalError $ mkErr mod "an initial size argument" args

    memType :: String -> [AExpr] -> ([Integer], [AExpr])
    memType _ ((ASInt _ _ sz1):(ASInt _ _ sz2):es) =
        ([ilValue sz1, ilValue sz2], es)
    memType mod args =
        internalError $ mkErr mod "addr and data width arguments" args

    memFileType :: String -> [AExpr] -> ([Integer], [AExpr])
    memFileType _ (str:(ASInt _ _ sz1):(ASInt _ _ sz2):es)
        | isStringType (ae_type str) = ([ilValue sz1, ilValue sz2], str:es)
    memFileType mod args =
        internalError $
            mkErr mod "filename and addr and data width arguments" args

    bramType :: String -> [AExpr] -> ([Integer], [AExpr])
    bramType _ (e1@(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):es) =
        ([ilValue sz1, ilValue sz2], e1:es)
    bramType mod args =
        internalError $ mkErr mod "addr and data width arguments" args

    bramFileType :: String -> [AExpr] -> ([Integer], [AExpr])
    bramFileType _ (str:e1@(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):es)
        | isStringType (ae_type str) = ([ilValue sz1, ilValue sz2], str:e1:es)
    bramFileType mod args =
        internalError $
            mkErr mod "filename and addr and data width arguments" args

    bramEnsType :: String -> [AExpr] -> ([Integer], [AExpr])
    bramEnsType _ (e1@(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):(ASInt _ _ _):(ASInt _ _ sz4):es) =
        -- sz3 is computable from sz1 and sz2, but we could still pass it?
        ([ilValue sz1, ilValue sz2, ilValue sz4], e1:es)
    bramEnsType mod args =
        internalError $ mkErr mod "BRAM byte enable and size arguments" args

    bramFileEnsType :: String -> [AExpr] -> ([Integer], [AExpr])
    bramFileEnsType _ (str:e1@(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):(ASInt _ _ _):(ASInt _ _ sz4):es)
        | isStringType (ae_type str) =
        -- sz3 is computable from sz1 and sz2, but we could still pass it?
        ([ilValue sz1, ilValue sz2, ilValue sz4], str:e1:es)
    bramFileEnsType mod args =
        internalError $
            mkErr mod "filename and BRAM byte enable and size arguments" args

-- -------------------------
