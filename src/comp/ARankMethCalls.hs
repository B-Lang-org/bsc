module ARankMethCalls(aRankMethCalls) where

import Data.List
import Data.Maybe
import Control.Monad(when)

import ASyntax
import FStringCompat
import Id
import Error(ErrMsg(..), ErrorHandle, bsError, bsWarning)
import Position
import Pragma

-- XXX first separate methods from rules so find doesn't fail

-- XXX need to do a deep copy of methods, because they might refer to
-- XXX the same local defs
-- XXX what do we do about rules?  should we require that they all be mentioned?
-- XXX or should they all be rank zero?

-- tag uses in methods for A&R "performance guarantees"
-- when ranks /= [], sets of method names such that each method in has
-- the same rank.  e.g., given PPperf_spec [[x,y],[z]], x and y would have
-- rank 0, and z would have rank 1.
-- for all the methods of rank 1, calls to methods of instantiated objects
-- have a __RANK_ suffix appended.
-- only methods mentioned in the rank list survive, and a warning
-- is issued if not all the methods are in the rank list.
-- mentioning multiple methods in the ranking or referring to
-- nonexistent methods is illegal.
-- when [], the all methods survive untouched.
aRankMethCalls :: ErrorHandle -> [PProp] -> APackage -> IO APackage
aRankMethCalls errh pprops orig_pkg =
    case [rs | PPperf_spec rs <- pprops] of
    [] -> return orig_pkg
    [ranks] -> aRankMethCallsInternal errh ranks orig_pkg
    (ranks:_:_) ->
        bsError errh
          [(getPosition ranks, EGeneric "Multiple (* perf_spec *) attributes forbidden")]

-- the guts of aRankMethCalls documented above
aRankMethCallsInternal :: ErrorHandle -> [[Id]] -> APackage -> IO APackage
aRankMethCallsInternal _ [] orig_pkg = return orig_pkg
aRankMethCallsInternal errh orig_ranks orig_pkg =
    do let method_map = [(aif_name m, m) | m <- apkg_interface orig_pkg]
           rule_map = [(dropRulePrefixId (arule_id r), r) | r <- apkg_rules orig_pkg]
           def_map = [(adef_objid d, d) | d <- apkg_local_defs orig_pkg]
           -- add method ready signals foreach method in (* perf_spec *)
           ranks_with_rdys = [concat [[m, mkRdyId m] | m <- rank] | rank <- orig_ranks]
           -- error checking:
           -- names mentioned in the rank attribute
           ranked_names = foldr union [] orig_ranks
           -- all rule and method names
           rule_method_names = [m | (m,_) <- method_map, not (isRdyId m)] ++
                               [r | (r,_) <- rule_map]
           -- names mentioned more than once
           multi_names = [m | (m:_:_) <- group (sort (concat orig_ranks))]
           unranked_names = rule_method_names \\ ranked_names
           bogus_names = ranked_names \\ rule_method_names
           show_with_commas names =
               intercalate ", " [show (getIdString n) | n <- names]
       when (not (null bogus_names))
           (bsError errh
            [(getPosition (head bogus_names),
              EGeneric ("(* perf_spec *) mentions nonexistent methods/rules: " ++
                       show_with_commas bogus_names))])
       when (not (null multi_names))
           (bsError errh
            [(getPosition (head multi_names),
             EGeneric ("Methods/rules mentioned multiple times in (* perf_spec *): "++
                       show_with_commas multi_names))])
       when (not (null unranked_names))
           (bsWarning errh
            [(getPosition (head unranked_names),
              EGeneric ("Methods/rules missing from (* perf_spec *): " ++
                        show_with_commas [m | m <- unranked_names,
                                              not (isRdyId m)]))])
       let find_def name = maybeToList (lookup name def_map)
           find_rule name = maybeToList (lookup name rule_map)
           find_meth name = maybeToList (lookup name method_map)
           -- rank local definitions and all defs they refer to
           cvt_defs v done_defs done_ids [] = done_defs
           cvt_defs v done_defs done_ids (def_id:def_ids)
               | def_id `elem` done_ids = cvt_defs v done_defs done_ids def_ids
               | otherwise =
                   let (ranked_def, more_def_ids) =
                           rankMethCalls v (find_def def_id)
                       fixup_name def@(ADef { adef_objid = name }) =
                           def { adef_objid = rankId v name }
                       -- XXX rename def LHS
                       new_def_ids = def_ids `union` (more_def_ids \\ done_ids)
                   in  cvt_defs v (map fixup_name ranked_def ++ done_defs)
                                (def_id:done_ids) new_def_ids
           -- convert methods and rules of the same rank, and local defs inside
           convert_one_rank ver meth_rule_names =
               let (methods, defs_to_rewrite_1) =
                       -- XXX rename LHS
                       rankMethCalls ver (concatMap find_meth meth_rule_names)
                   (rules, defs_to_rewrite_2) =
                       -- XXX rename LHS
                       rankMethCalls ver (concatMap find_rule meth_rule_names)
                   defs_to_rewrite = defs_to_rewrite_1 `union` defs_to_rewrite_2
                   defs = cvt_defs ver [] [] defs_to_rewrite
               in  (methods, rules, defs)
           (methss, ruless, defss) =
               unzip3 [convert_one_rank ver meths_rules
                       | (meths_rules, ver) <- zip ranks_with_rdys [0..]]
           -- add methods not mentioned in performance spec
           unranked_names_with_rdys =
               concat [[m, mkRdyId m] | m <- unranked_names]
           unranked_meths = concatMap find_meth unranked_names_with_rdys
--       mapM_ (traceM . ('\n' :) . show) ranked_ifc
       return (orig_pkg { apkg_interface = concat methss ++ unranked_meths,
                          apkg_rules = concat ruless,
                          apkg_local_defs = concat defss })

-- class of types which contain methods and method calls with a function
-- to append a rank to all method definitions and calls
-- returns rewritten ats plus local definitions which need ranking
class RankMethCalls ats_t where
    rankMethCalls :: Int -> ats_t -> (ats_t, [Id] {- local defs to rank -})

instance RankMethCalls AExpr where
    rankMethCalls ver expr@(AMethCall { ameth_id = name, ae_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (expr { ameth_id = rankId ver name, ae_args = ranked_args  },
             defs_to_rewrite)
    rankMethCalls ver expr@(AMethValue { ameth_id = name }) =
        (expr { ameth_id = rankId ver name }, [])
    rankMethCalls ver expr@(ATuple { ae_elems = elems }) =
        let (ranked_elems, defs_to_rewrite) = rankMethCalls ver elems
        in  (expr { ae_elems = ranked_elems }, defs_to_rewrite)
    rankMethCalls ver expr@(ATupleSel { ae_exp = e }) =
        let (ranked_e, defs_to_rewrite) = rankMethCalls ver e
        in  (expr { ae_exp = ranked_e }, defs_to_rewrite)
    rankMethCalls ver expr@(ANoInlineFunCall { ae_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (expr { ae_args = ranked_args }, defs_to_rewrite)
    rankMethCalls ver expr@(AFunCall { ae_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (expr { ae_args = ranked_args }, defs_to_rewrite)
    rankMethCalls ver expr@(APrim { ae_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (expr { ae_args = ranked_args }, defs_to_rewrite)
    rankMethCalls ver expr@(ASDef { ae_objid = name }) | not (isRdyId name) =
        (expr { ae_objid = rankId ver name }, [name])
    rankMethCalls ver expr = (expr, [])

instance RankMethCalls ADef where
    rankMethCalls ver def@(ADef { adef_expr = body }) =
        let (ranked_body, defs_to_rewrite) = rankMethCalls ver body
        in  (def { adef_expr = ranked_body }, defs_to_rewrite)

instance RankMethCalls AIFace where
    rankMethCalls ver meth@(AIDef { aif_value = value, aif_pred = pred,
                                     aif_inputs = inputs,
                                     aif_fieldinfo = fi }) =
        let (ranked_value, defs_to_rewrite_1) = rankMethCalls ver value
            (ranked_pred, defs_to_rewrite_2) = rankMethCalls ver pred
            defs_to_rewrite = defs_to_rewrite_1 `union` defs_to_rewrite_2
        in  (meth { aif_value = ranked_value, aif_pred = ranked_pred },
             defs_to_rewrite)
    rankMethCalls ver meth@(AIAction { aif_pred = pred, aif_body = body }) =
        let (ranked_body, defs_to_rewrite_1) = rankMethCalls ver body
            (ranked_pred, defs_to_rewrite_2) = rankMethCalls ver pred
            defs_to_rewrite = defs_to_rewrite_1 `union` defs_to_rewrite_2
        in  (meth { aif_pred = ranked_pred, aif_body = ranked_body },
             defs_to_rewrite)
    rankMethCalls ver meth = (meth, []) -- clock and reset

instance RankMethCalls ARule where
    rankMethCalls ver rule@(ARule { arule_pred = pred, arule_actions = acts }) =
        let (ranked_pred, defs_to_rewrite_1) = rankMethCalls ver pred
            (ranked_acts, defs_to_rewrite_2) = rankMethCalls ver acts
            defs_to_rewrite = defs_to_rewrite_1 `union` defs_to_rewrite_2
        in  (rule { arule_pred = ranked_pred, arule_actions = ranked_acts },
             defs_to_rewrite)

instance RankMethCalls AAction where
    rankMethCalls ver act@(ACall { acall_methid = meth, aact_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (act { acall_methid = rankId ver meth, aact_args = ranked_args },
             defs_to_rewrite)
    rankMethCalls ver act@(AFCall { aact_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (act { aact_args = ranked_args }, defs_to_rewrite)
    rankMethCalls ver act@(ATaskAction { aact_args = args }) =
        let (ranked_args, defs_to_rewrite) = rankMethCalls ver args
        in  (act { aact_args = ranked_args }, defs_to_rewrite)

instance (RankMethCalls elt_t) => RankMethCalls [elt_t] where
    rankMethCalls ver elts =
        let ranked_pairs = [rankMethCalls ver elt | elt <- elts]
        in  (map fst ranked_pairs, foldr (union . snd) [] ranked_pairs)

rankId :: Int -> Id -> Id
rankId rank name =
    mkIdPost name (mkFString $ rankSuffix rank)

rankSuffix :: Int -> String
rankSuffix rank  ="__RANK_" ++ show rank
