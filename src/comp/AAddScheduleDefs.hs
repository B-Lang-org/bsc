module AAddScheduleDefs (aAddScheduleDefs) where

import ASyntax
import ASyntaxUtil
import AScheduleInfo
import AUses
import Flags
import Pragma
import ProofObligation(ProofObligation(..), ProofResult(..), MsgFn(..),
                       MsgTuple, warnUnlessProof, errorUnlessProof)
import PFPrint
import Error(ErrMsg(..))
import ErrorUtil(internalError)
import VModInfo(VModInfo(..), VFieldInfo(..), VeriPortProp(..), mkNamedEnable)
import Id (Id, getIdString, isRdyId, dropReadyPrefixId,
           mkIdWillFire, mkIdCanFire, mkRdyId)
import Position
import BackendNamingConventions
import PreIds(id_write)

import qualified Data.Map as M

import Data.List(intersect)
import Data.Maybe(fromJust, fromMaybe, maybeToList, mapMaybe)

-- import Debug.Trace

-- -------------------------------------------------------------------
-- This file contains all of the logic for creating defs describing
-- the schedule for a module.
--
-- The explicit and implicit conditions which control when a rule
-- can fire are used to define the CAN_FIRE signal for that rule.
--
-- The urgency and conflict information from scheduling is added
-- to the CAN_FIRE to produce the WILL_FIRE signal for rules.
--
-- So for user-generated rules, we have:
--  CAN_FIRE_rule = predicate for rule
--  WILL_FIRE_rule = CAN_FIRE_RULE &&
--                   !(WILL_FIRE of any conflicting more urgent rule) &&
--                   !(RDY of any conflicting more urgent value method)
--
-- Methods are more complicated.  Action and ActionValue methods
-- are converted to rules -- possibly multiple rules per method.
-- Their rules have CAN_FIRE signals which combine the method's
-- predicates with additional logic to select which rule to execute
-- out of all of the rules associated with a method.
--
-- The scheduling logic combined with the CAN_FIRE signals of the
-- associated rules is used to create the ready (RDY) value for
-- each method.
--
-- The WILL_FIRE signals for Action or ActionValue method rules
-- combine the CAN_FIRE with the enable (EN) port.  Since
-- (!RDY ==> !EN), the WILL_FIRE gets its selection logic through
-- the CAN_FIRE and the scheduling logic through the EN.
--
-- So for Action and ActionValue methods we have:
--   RDY_method = some associated rule has CAN_FIRE true and
--                !(WILL_FIRE of any conflicting rule more urgent
--                  than that rule)
--   EN_method  = input port or constant
-- And for each rule associated with the Action or ActionValue method:
--   CAN_FIRE_rule = method predicate && rule selection logic
--   WILL_FIRE_rule = CAN_FIRE_rule && EN_method
--
-- In the common case of a single rule per method, the WILL_FIRE can
-- be optimized to be simply the EN value, since no selection is
-- required through the CAN_FIRE signal.
--
-- Value methods have only a RDY value, which is the method's predicate
-- augmented with the !WILL_FIRE for any conflicting more urgent rules.
--
-- The RDY value for methods does not need to account for any
-- conflicting methods because method-method conflicts are handled
-- externally by way of scheduling annotations on the interface.
--
-- In addition to creating the schedule defs, we accumulate a set of
-- proof obligations related to always_ready and enabled_when_ready
-- methods.  The obligations are later checked to provide feedback
-- to the user.  The obligation is that a method which is always
-- ready must have a true RDY condition.

type ExprMap = M.Map Id AExpr

aAddScheduleDefs :: Flags -> [PProp] -> APackage -> AScheduleInfo ->
                    IO APackage
aAddScheduleDefs flags pps pkg aschedinfo =
  do
     -- Collect some useful information
     let defs0     = apkg_local_defs pkg
         rules0    = apkg_rules pkg
         ifc0      = apkg_interface pkg
         insts0    = apkg_state_instances pkg
         proofs0   = apkg_proof_obligations pkg
         asched    = asi_schedule aschedinfo
         conflicts = concatMap getConflictList (asch_scheduler asched)
         mumap     = asi_method_uses_map aschedinfo
         -- for error messages
         pkgpos    = getPosition (apkg_name pkg)

     -- Build maps for ready and enable values and collect
     -- proof obligations associated with always_ready, always_en, etc.
     -- The ExprMaps map from a method name (not RDY) to the expression
     -- for that method's ready or enable condition.
     let pre_rdy_map = M.fromList $
                       [ (dropReadyPrefixId (aif_name m), adef_expr $ aif_value m)
                       | m <- ifc0
                       , isRdyId (aif_name m)
                       ]
         pre_en_map  = M.fromList $
                       [ (aif_name m, e)
                       | m <- ifc0
                       , (Just e) <- [getMethodEnExpr m]
                       ]
         (rdy_map, rdy_proof_obs) =
             handleAlwaysReady (unsafeAlwaysRdy flags) pkgpos pps pre_rdy_map
         (en_map, enrdy_proof_obs) =
             handleEnableWhenReady pps rdy_map pre_en_map

     -- Build proof obligations for always_enabled methods of submodules
     let ensub_proof_obs = handleSubmodAlwaysEnabled mumap insts0

     let proofs1        = proofs0 ++ rdy_proof_obs ++ enrdy_proof_obs ++
                          ensub_proof_obs

     -- Handle user-generated rules by building CAN_FIREs
     -- from their predicates and WILL_FIREs from the conflict
     -- information
     let user_cfs = map mkUserCF rules0
         user_wfs = map (mkUserWF conflicts) rules0

     -- Build CAN_FIREs for interface rules based on the
     -- method predicates and rule selection logic.  Use the
     -- CAN_FIREs and EN ports to build WILL_FIREs for the
     -- interface rules.  For value methods, the WILL_FIRE is the RDY.
     let ifc_cfs = concatMap (mkIfcCFs rdy_map) ifc0
         ifc_wfs = concatMap (mkIfcWFs en_map rdy_map) ifc0

     -- Update the RDY values for each method
     let rule_map       = mapMaybe buildRuleMap ifc0
         rule_names     = map aRuleName rules0
         rule_conflicts = [ (n, cs `intersect` rule_names)
                          | (n,cs) <- conflicts
                          ]
         ifc1           = map (replaceReadyExpr rule_map rule_conflicts) ifc0

     -- Rewrite all rule predicates to use WILL_FIRE values
     let rules1 = map replaceRulePredicate rules0
         ifc2   = map replaceIfcRulePredicates ifc1

     -- return a modified APackage
     let cf_defs = user_cfs ++ ifc_cfs
         wf_defs = user_wfs ++ ifc_wfs
         defs1   = defs0 ++ cf_defs ++ wf_defs

     return pkg { apkg_local_defs        = defs1
                , apkg_rules             = rules1
                , apkg_interface         = ifc2
                , apkg_proof_obligations = proofs1
                }

-- Helper function for use with looking up list values
ll :: (Eq a) => a -> [(a,[b])] -> [b]
ll x ps = fromMaybe [] (lookup x ps)

-- Get the list of conflicts from a schedule
getConflictList :: AScheduler -> [(ARuleId, [ARuleId])]
getConflictList (ASchedEsposito cs) = cs

-- Get the enable expression for a method
getMethodEnExpr :: AIFace -> Maybe AExpr
getMethodEnExpr (AIAction      { aif_fieldinfo = fi}) =
  Just (aBoolPort (mkNamedEnable fi))
getMethodEnExpr (AIActionValue { aif_fieldinfo = fi}) =
  Just (aBoolPort (mkNamedEnable fi))
getMethodEnExpr _ = Nothing

-- Unless expr is true, warn/error about "not always ready"
mustBeTrue :: Bool -> Position -> Id -> AExpr -> (ProofObligation AExpr, MsgFn)
mustBeTrue warn pkgpos m e =
  let po  = ProveEq e aTrue
      msg = (pkgpos, ENotAlwaysReady (getIdString m))
      fn  = (if warn then warnUnlessProof else errorUnlessProof) [msg]
  in (po, MsgFn "ENotAlwaysReady" fn)

-- Apply properties that modify ready values by updating the ExprMap
-- entries and accumulating associated proof obligations.
handleAlwaysReady :: Bool -> Position -> [PProp] -> ExprMap ->
                     (ExprMap,[(ProofObligation AExpr, MsgFn)])
handleAlwaysReady warn pkgpos pps pre_rdy_map =
  let (m, proofs) = unzip (map doRdy (M.toList pre_rdy_map))
  in (M.fromList m, concat proofs)
  where doRdy (n,e) | isAlwaysRdy pps (mkRdyId n) =
          ((n,e), [mustBeTrue warn pkgpos n e])
        doRdy (n,e) = ((n,e),[])

handleEnableWhenReady :: [PProp] -> ExprMap -> ExprMap ->
                         (ExprMap,[(ProofObligation AExpr, MsgFn)])
handleEnableWhenReady pps rdy_map pre_en_map =
  let (m, proofs) = unzip (map doEn (M.toList pre_en_map))
  in (M.fromList m, concat proofs)
  where doEn (n,e) | isEnWhenRdy pps n
           = ((n, fromMaybe e (n `M.lookup` rdy_map)),[])
        doEn (n,e) = ((n,e),[])

-- Build conflict expr (CF && !WFs)
buildConflictExpr :: Id -> [Id] -> AExpr
buildConflictExpr name conflicts =
  let cf    = aBoolVar (mkIdCanFire name)
      wfs  = [ aBoolVar (mkIdWillFire i) | i <- conflicts ]
  in  aAnds (cf : map aNot wfs)

-- Create a CAN_FIRE def for a rule based on the rule predicate
mkUserCF :: ARule -> ADef
mkUserCF r = ADef (mkIdCanFire rule) aTBool (aRulePred r) [DefP_Rule rule]
             where rule = aRuleName r

-- Create a WILL_FIRE def for a rule from its CAN_FIRE and
-- conflicting WILL_FIREs and RDYs
mkUserWF :: [(Id,[Id])] -> ARule -> ADef
mkUserWF conflicts r =
  let rid       = aRuleName r
      cs        = ll rid conflicts
      e         = buildConflictExpr rid cs
  in ADef (mkIdWillFire rid) aTBool e [DefP_Rule rid]

-- Create CAN_FIRE defs for a method's rules based on its
-- method predicate and the rule selection logic.
mkIfcCFs :: ExprMap -> AIFace -> [ADef]
mkIfcCFs rdy_map (AIAction { aif_name = n, aif_body = rs }) =
  let rdy_expr = fromJust (M.lookup n rdy_map)
  in [ ADef (mkIdCanFire (aRuleName r)) aTBool (aAnd rdy_expr (aRulePred r))
       [DefP_Rule (aRuleName r)]
     | r <- rs
     ]
mkIfcCFs rdy_map (AIActionValue { aif_name = n, aif_body = rs }) =
  let rdy_expr = fromJust (M.lookup n rdy_map)
  in [ ADef (mkIdCanFire (aRuleName r)) aTBool (aAnd rdy_expr (aRulePred r))
       [DefP_Rule (aRuleName r)]
     | r <- rs
     ]
mkIfcCFs rdy_map (AIDef { aif_name = n }) | not (isRdyId n) =
  let rdy_expr = fromJust (M.lookup n rdy_map)
  in  [ ADef (mkIdCanFire n) aTBool rdy_expr [DefP_Rule n] ]
mkIfcCFs _ _ = []  -- ignore RDY methods, clocks, resets, inouts

-- Helper function to create WILL_FIREs for interface rules
mkOneWF :: Id -> [AExpr] -> ARule -> ADef
mkOneWF method_name en_exprs (ARule {arule_id = rule_name}) =
  let cf_exprs = [aBoolVar (mkIdCanFire rule_name)]
  in ADef (mkIdWillFire rule_name) aTBool (aAnds (cf_exprs ++ en_exprs))
     [DefP_Rule rule_name]

-- Create WILL_FIRE defs for a method's rules based on its
-- CAN_FIRE and the method EN.
mkIfcWFs :: ExprMap -> ExprMap -> AIFace -> [ADef]
mkIfcWFs en_map _ (AIAction { aif_name = n, aif_body = [r] }) =
  let en_exprs = maybeToList (M.lookup n en_map)
      rule = aRuleName r
  in [ ADef (mkIdWillFire rule) aTBool (aAnds en_exprs)
       [DefP_Rule rule] ]
mkIfcWFs en_map _ (AIAction { aif_name = n, aif_body = rs }) =
  let en_exprs = maybeToList (M.lookup n en_map)
  in map (mkOneWF n en_exprs) rs
mkIfcWFs en_map _ (AIActionValue { aif_name = n, aif_body = [r] }) =
  let en_exprs = maybeToList (M.lookup n en_map)
      rule = aRuleName r
  in [ ADef (mkIdWillFire rule) aTBool (aAnds en_exprs)
       [DefP_Rule rule] ]
mkIfcWFs en_map _ (AIActionValue { aif_name = n, aif_body = rs }) =
  let en_exprs = maybeToList (M.lookup n en_map)
  in map (mkOneWF n en_exprs) rs
mkIfcWFs _ rdy_map (AIDef { aif_name = n }) | not (isRdyId n) =
  let rdy_expr = fromJust (M.lookup n rdy_map)
  in  [ ADef (mkIdWillFire n) aTBool rdy_expr [DefP_Rule n]]
mkIfcWFs _ _ _ = []  -- ignore RDY methods, clocks, resets, inouts

-- Get the map from a method to its rule names (or def name, for value method)
buildRuleMap :: AIFace -> Maybe (Id, [Id])
buildRuleMap m@(AIAction {}) =
    Just (aif_name m, map aRuleName (aIfaceRules m))
buildRuleMap m@(AIActionValue {}) =
    Just (aif_name m, map aRuleName (aIfaceRules m))
buildRuleMap m@(AIDef { aif_name = mid }) | not (isRdyId mid) =
    Just (mid, [aif_name m])
buildRuleMap _ = Nothing

-- Replace the value in a RDY method
replaceReadyExpr :: [(Id,[Id])] -> [(Id,[Id])] -> AIFace -> AIFace
replaceReadyExpr rule_map rule_conflicts m@(AIDef { aif_name = n })
  | isRdyId n =
    let mn = dropReadyPrefixId n
        v  = aif_value m
        v' = case lookup mn rule_map of
              Nothing -> internalError ("replaceReadyExpr: no value for " ++
                                        ppReadable mn)
              (Just []) -> internalError ("replaceReadyExpr: no rules for " ++
                                          ppReadable mn)
              (Just rids) ->
                  -- for Action/ActionValue methods, the new RDY value is
                  -- the OR of conflict exprs for each rule, where the
                  -- conflict expr is "CF_rid && !WF_blockers".  For value
                  -- methods, the RDY is just the conflict expr, using the
                  -- method Id instead of the rule Ids.
                  let e = aOrs [ buildConflictExpr rid (ll rid rule_conflicts)
                                 | rid <- rids ]
                  in v { adef_expr = e }
    in m { aif_value = v' }
replaceReadyExpr _ _ x = x

-- Replace the predicate in a rule with a reference to the
-- rule's CAN_FIRE def.
replaceRulePredicate :: ARule -> ARule
replaceRulePredicate r =
  let cf_id = mkIdCanFire (aRuleName r)
  in r { arule_pred = (aBoolVar cf_id) }

-- Replace the predicate in all the rules of a method with a
-- reference to the rule's CAN_FIRE def.
replaceIfcRulePredicates :: AIFace -> AIFace
replaceIfcRulePredicates m@(AIAction { aif_body = rs }) =
  m { aif_body = map replaceRulePredicate rs }
replaceIfcRulePredicates m@(AIActionValue { aif_body = rs }) =
  m { aif_body = map replaceRulePredicate rs }
replaceIfcRulePredicates m = m

 -- -------------------------

handleSubmodAlwaysEnabled :: MethodUsesMap -> [AVInst] ->
                             [(ProofObligation AExpr, MsgFn)]
handleSubmodAlwaysEnabled mumap insts =
  let
      always_en_methods =
        [ (i, m, m_renamed)
          | avinst <- insts,
            let i = avi_vname avinst,
            let vi = avi_vmi avinst,
            (Method m _ _ _ _ _ (Just (_, vps))) <- vFields vi,
            VPinhigh `elem` vps,
            -- For some primitives, the user sees a different ifc
            -- than what is imported, because of a wrapper
            -- XXX right now we just handle BypassWire
            -- XXX there should be a more general renaming mechanism
            let m_renamed = if (isBypassWire avinst || isBypassWire0 avinst)
                            then id_write (getPosition i)
                            else m
            -- if we want to report the EN signal name?
            -- mkEnId m (if mult > 1 then map Just [0..mult-1] else [Nothing])
        ]

      makeAlwaysEnProof (i, m, m_renamed) =
        let
            mid = MethodId i m
            mkWF = ASDef aTBool . mkIdWillFire
            uses = [ aAnd cond (aOrs wfs)
                     | Just use_info <- [M.lookup mid mumap],
                       -- only action uses have EN
                       (use, (_, act_users@(_:_), _)) <- use_info,
                       let cond = extractCondition use,
                       let wfs = map mkWF act_users
                   ]
            -- This expression needs to be always True
            use_expr = if (null uses) then aFalse else (aOrs uses)

            -- Construct the MsgFn for the ProofObligation

            -- user-visible names for the error messages
            i_str = pfpString i
            m_str = pfpString m_renamed

            insertMethod m [] = [m]
            insertMethod m (m2:ms) =
                case (compare m m2) of
                  LT -> (m:m2:ms)
                  EQ -> (m2:ms)
                  GT -> (m2:insertMethod m ms)

            disproveMsg = (getPosition i, EEnableAlwaysLow i_str [m_str])

            insertDisproveMsg [] = [disproveMsg]
            insertDisproveMsg (msg2@(pos, EEnableAlwaysLow i2_str ms):rest) =
                case (compare i_str i2_str) of
                  LT -> (disproveMsg:msg2:rest)
                  EQ -> let ms' = insertMethod m_str ms
                        in  ((pos, EEnableAlwaysLow i2_str ms'):rest)
                  GT -> (msg2:insertDisproveMsg rest)
            insertDisproveMsg (msg2:rest) =
                -- could be EEnableNotHigh
                (msg2:insertDisproveMsg rest)

            inconclusiveMsg = (getPosition i, EEnableNotHigh i_str [m_str])

            insertInconclusiveMsg [] = [inconclusiveMsg]
            insertInconclusiveMsg (msg2@(pos, EEnableNotHigh i2_str ms):rest) =
                case (compare i_str i2_str) of
                  LT -> (inconclusiveMsg:msg2:rest)
                  EQ -> let ms' = insertMethod m_str ms
                        in  ((pos, EEnableNotHigh i2_str ms'):rest)
                  GT -> (msg2:insertInconclusiveMsg rest)
            insertInconclusiveMsg (msg2:rest) =
                -- could be EEnableAlwaysLow
                (msg2:insertInconclusiveMsg rest)

            -- allow the user to demote these errors
            msgFn :: ProofResult -> MsgTuple -> MsgTuple
            msgFn Proven (ws, ds, es) = (ws, ds, es)
            msgFn Disproven (ws, ds, es) = (ws, insertDisproveMsg ds, es)
            msgFn Inconclusive (ws, ds, es) = (insertInconclusiveMsg ws, ds, es)
        in
            -- XXX if there are no users
            -- XXX then we could report the error right away
            (ProveEq use_expr aTrue, MsgFn "EEnableNotHigh" msgFn)
  in
      map makeAlwaysEnProof always_en_methods

-- -------------------------
