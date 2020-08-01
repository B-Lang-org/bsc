{-# LANGUAGE CPP #-}
module IDropRules (iDropRules) where

import qualified Data.Set as S
import qualified Data.Map.Lazy as M
import Data.List(partition, find)
import Control.Monad(when)

import IntLit
import Position
import Id
import Flags(Flags, removeFalseRules, removeEmptyRules, warnUndetPred)
import Pragma
import Error(internalError, ErrMsg(..), ErrorHandle, bsWarning)
import ISyntax
import Prim
import VModInfo(VFieldInfo(..))
import Util(fromJustOrErr)
import PPrint


-- Handle rules that don't do anything,
-- either because the predicate is False or the body has no actions.
-- Any MethodPred signals associated with the dropped rules are dropped.
--
-- Warn the user about false/empty rules.  If the appropriate flag is set,
-- the rules are dropped.
--
-- False/empty rules that resulted from rule splitting are removed
-- regardless of the flag and no warning is issued.
--
-- Removing a noAction rule can only be done if the rule is not preempting
-- another rule (unless that rule is also noAction).
--
-- we don't drop any method rule bodies here
-- because the backend can't deal with methods
-- that have empty action bodies
--
iDropRules :: ErrorHandle -> Flags -> IModule a -> IO (IModule a)
iDropRules errh flags imod0 = do
  imod1 <- dropFalseRules errh flags imod0
  imod2 <- dropEmptyRules errh flags imod1
  warnUndetPreds errh flags imod2
  return imod2

dropFalseRules :: ErrorHandle -> Flags -> IModule a -> IO (IModule a)
dropFalseRules errh flags imod@(IModule { imod_rules = (IRules sps rs),
                                          imod_local_defs = ds }) = do
    -- identify false rules
    let (falseRules, okRules) = partition isFalseRule rs

    -- we treat the split rules differently, so separate them out
    let (splitFalseRules, nonsplitFalseRules) =
            partition isSplitRule falseRules

    -- warn about the non-split False rules
    let removeFalseRule = removeFalseRules flags
    let warnFalseRule (IRule {
               irule_name = rid , irule_pragmas = pragmas } ) =
           if (RPnoWarn `elem` pragmas)
           then return ()
           else bsWarning errh
                    [(getPosition rid,
                      WRuleAlwaysFalse (dropRulePrefix rid) removeFalseRule)]
    mapM_ warnFalseRule nonsplitFalseRules

    -- the final set of kept rules and dropped rules, depending on the flag
    let (rs', dropped_rules) =
            if removeFalseRule
            then -- all False rules are dropped
                 (okRules, falseRules)
            else -- keep the non-split rules, but always drop the split rules
                 (okRules ++ nonsplitFalseRules, splitFalseRules)

    -- drop the pragmas and defs associated with the dropped rules
    let dropped_rule_ids = map getIRuleId dropped_rules
        sps' = removeSchedPragmaIds dropped_rule_ids sps
        ds' = removeIDefMethodPredsByRuleId dropped_rule_ids ds

    return $ imod { imod_rules       = (IRules sps' rs')
                  , imod_local_defs  = ds'
                  }


dropEmptyRules :: ErrorHandle -> Flags -> IModule a -> IO (IModule a)
dropEmptyRules errh flags imod@(IModule { imod_rules = (IRules sps rs),
                                          imod_local_defs = ds }) = do
    -- identify empty rules which do not preempt other rules (in sps)
    let (emptyNonPreemptRules, okRules) =
            partition (\r -> isNoActionRule r &&
                             not (isRulePreempt (getIRuleId r) sps))
                rs

    -- we treat the split rules differently, so separate them out
    let (splitEmptyRules, nonsplitEmptyRules) =
          partition isSplitRule emptyNonPreemptRules

    -- warn about the empty rules
    let removeEmptyRule = removeEmptyRules flags
    let warnEmptyRule ( IRule {
              irule_name = rid , irule_pragmas = pragmas } )=
           if (RPnoWarn `elem` pragmas)
           then return ()
           else bsWarning errh
                    [(getPosition rid,
                      WRuleNoActions (dropRulePrefix rid) removeEmptyRule)]
    mapM_ warnEmptyRule nonsplitEmptyRules

    -- the final set of kept rules and dropped rules, depending on the flag
    let (rs', dropped_rules) =
            if removeEmptyRule
            then -- all empty rules are dropped
                 (okRules, emptyNonPreemptRules)
            else -- keep the non-split rules, but always drop the split rules
                 (okRules ++ nonsplitEmptyRules, splitEmptyRules)

    -- drop the pragmas and defs associated with the dropped rules
    let dropped_rule_ids = map getIRuleId dropped_rules
        sps' = removeSchedPragmaIds dropped_rule_ids sps
        ds' = removeIDefMethodPredsByRuleId dropped_rule_ids ds

    return $ imod { imod_rules       = (IRules sps' rs')
                  , imod_local_defs  = ds'
                  }


-- will the rule never fire
isFalseRule :: IRule a -> Bool
isFalseRule (IRule { irule_pred =
               (ICon _ (ICInt { iVal = (IntLit { ilValue = 0 }) }))
                   } )
              = True
isFalseRule _ = False

-- is the rule a result of splitting
isSplitRule :: IRule a -> Bool
isSplitRule r = isSplitRuleId (getIRuleId r)

-- is the rule a noAction rule
isNoActionRule :: IRule a -> Bool
isNoActionRule (IRule {
       irule_body = (ICon _ (ICPrim { primOp = PrimNoActions })) } )
    = True
isNoActionRule _ = False


removeIDefMethodPredsByRuleId :: [Id] -> [IDef a] -> [IDef a]
removeIDefMethodPredsByRuleId [] ds = ds
removeIDefMethodPredsByRuleId dropped_rule_ids ds =
    let
        dropped_id_set = S.fromList dropped_rule_ids

        isRuleProp (DefP_Rule {}) = True
        isRuleProp _              = False

        isForDroppedRule ps =
            case (find isRuleProp ps) of
              Just (DefP_Rule r) -> r `S.member` dropped_id_set
              _ -> internalError ("MethodPred with no DefP_Rule")

        dropDef (IDef i _ _ ps) =
            (hasIdProp i IdPMethodPredicate) &&
            (isForDroppedRule ps)
    in
        filter (not . dropDef) ds


warnUndetPreds :: ErrorHandle -> Flags -> IModule a -> IO ()
warnUndetPreds errh flags imod | not (warnUndetPred flags) = return ()
warnUndetPreds errh flags imod@(IModule { imod_rules = (IRules _ rs),
                                          imod_interface = ms,
                                          imod_local_defs = ds }) = do
    let
        hmap = M.fromList [ (i, findUndets e) | (IDef i _ e _) <- ds ]

        -- this returns a list of positions for any undet values found
        findUndets :: IExpr a -> [Position]
        findUndets (IAps f _ as) = findUndets f ++ concatMap findUndets as
        findUndets (ICon i (ICUndet {})) = [getPosition i]
        findUndets (ICon i (ICValue {})) =
            fromJustOrErr ("findUndets: " ++ ppReadable i) $ M.lookup i hmap
        findUndets (ICon _ _) = []
        findUndets e = internalError ("warnUndetCond: " ++ ppReadable e)

{-      -- for trace output of an expression containing an undet
        dmap = M.fromList [ (i, e) | (IDef i _ e _) <- ds ]
        expandExpr (IAps f ts as) = (IAps (expandExpr f) ts (map expandExpr as))
        expandExpr (ICon i (ICValue {})) =
            expandExpr $
                fromJustOrErr ("expandExpr: " ++ ppReadable i) $ M.lookup i dmap
        expandExpr e = e
-}
    let
        (rdy_ms, actual_ms) = partition (isRdyId . ief_name) ms
        rdymap = M.fromList [ (i,e) | (IEFace i _ (Just (e, t)) _ _ _) <- rdy_ms ]
        getRdy i = fromJustOrErr ("getRdy: " ++ ppReadable i) $
                       M.lookup (mkRdyId i) rdymap

        warn i is_meth name poss =
            let keepFn p = (p /= noPosition) && (isUsefulPosition p)
                poss' = filter keepFn poss
            in  bsWarning errh [(getPosition i, WRuleUndetPred is_meth name poss')]

        -- if it's a method, 'rdy_poss' contains any positions from the RDY method
        checkRule is_meth rdy_poss (IRule { irule_name = rid, irule_pred = e }) = do
            let name = if is_meth
                       then (getIdString rid) else (dropRulePrefix rid)
            let undet_poss = rdy_poss ++ findUndets e
            when (not (null undet_poss)) $
                warn rid is_meth name undet_poss

        checkMethod (IEFace i _ _ maybe_rs _ (Method {})) = do
            let rdy_undet_poss = findUndets (getRdy i)
            case maybe_rs of
              Nothing ->
                  when (not (null rdy_undet_poss)) $
                      warn i True (getIdString i) rdy_undet_poss
              Just (IRules _ meth_rs) ->
                  mapM_ (checkRule True rdy_undet_poss) meth_rs
        checkMethod _ = return ()  -- Clock, Reset, Inout are OK

    mapM_ (checkRule False []) rs
    mapM_ checkMethod actual_ms
