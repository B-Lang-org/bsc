{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module ISplitIf (iSplitIf) where

import ISyntax
import Prim
import ErrorUtil(internalError)
import PPrint
import PreIds(idPrimExpIf, idActionValue_, idAVValue_)
import qualified Flags(Flags, expandIf)
import Position
import ISyntaxUtil
import Id(Id, mkSplitId, getIdString)
import Pragma(SPIdSplitMap, splitSchedPragmaIds)
import ITransform(iTransBoolExpr)
import PreStrings(fs_T, fs_F)
import FStringCompat(FString, concatFString, getFString, mkFString)
import Control.Monad(msum)
import Util(makePairs, flattenPairs)
import Util(mapSnd)
import Data.List(genericLength)
-- import Debug.Trace(trace)

-- --------------------------

-- Old comment from Ken:
--   Input there should be no dirty wrappers: check_dirty_if_wrappers
--   then push is called
--   Then, there should be no deepsplit wrapper
--   (Depending on exactly how I do it in push: there might be a point where
--   there are no shallow nosplit wrappers; any IF that is not wrapped is
--   assumed shallow nosplit)
--   (Otherwise, every If should be annotated)
--   After splitif is called, then there should be no wrappers.

iSplitIf :: Flags.Flags -> IModule a -> IModule a
iSplitIf flags imod@(IModule { imod_rules = rules,
                               imod_interface = methods })
  = --trace ("iSplitIf happens!") $
    let
       (smaps, new_methods) = unzip $ map (iSplitIface flags) methods
       -- provide the method split map, in case any rule pragmas mention methods
       (_, new_rules) = do_iExpandIfRules flags (concat smaps) rules
    in case check_rules isIfWrapper new_rules of
          (Just x) -> internalError ("iSplitIf Error " ++ (ppReadable x))
          _
              ->  case (msum (map (check_meth_rules isIfWrapper)
                                  new_methods)) of
                    (Just x) -> internalError ("iSplitIf Error in interface "
                                               ++ (ppReadable x))
                    _ -> --trace ("============m1\n"++(show new_methods)) $
                         imod { imod_rules = new_rules ,
                                imod_interface = new_methods }

-- --------------------------

-- expand `if' in rules to multiple rules
do_iExpandIfRules :: Flags.Flags -> SPIdSplitMap -> IRules a ->
                     (SPIdSplitMap, IRules a)
do_iExpandIfRules flags method_split_map (IRules sps rs)
  = --trace ("ie before : " ++ (ppReadable rs)) $
    --trace ("ie kenta  : " ++ (ppReadable m1)) $
    (idsplitmap, IRules sps' rs')
  where xs = unzip m1
        m1 = map (iExpandIfRule flags) rs
        idsplitmap = concat (fst xs)
        rs' = concat (snd xs)
        sps' = splitSchedPragmaIds (method_split_map ++ idsplitmap) sps

data Branch_taken a =
       -- if expr:
       -- the predicate, the branch taken (indicated by True or False)
       -- (the branch value will be used to name the split rule)
       BranchIf (IExpr a) Bool
       -- array selection, in bounds:
       -- index expr, element index taken, bit-width of index, pos of the op
       | BranchArrSel (IExpr a) Integer Integer Position
       -- array selection, out of bounds:
       -- index expr, number of elements, bit-width of index, pos of the op
       | BranchArrSelOutOfBounds (IExpr a) Integer Integer Position
       -- case expr, explicit arm:
       -- case index, arm expr that matches, bit-width of index, and
       -- number of the arm (for rule naming purposes)
       | BranchCase (IExpr a) (IExpr a) Integer Integer
       -- case expr, default arm:
       -- case index, all arm exprs that didn't match, bit-width of index
       | BranchCaseDefault (IExpr a) [IExpr a] Integer
    deriving (Ord, Eq, Show)

type Path_through_actions a = ([Branch_taken a],[IExpr a])

run :: forall itype . IExpr itype -> [Path_through_actions itype]
-- this function does the work of splitting an if into two actions

-- this function uses the list as the nondeterminism monad.  I've heard
-- that there exist more efficient nondeterminism monads, which should be
-- looked into if performance is a problem.

-- we are very careful of checking that the type arguments to
-- PrimExpIf, PrimNoExpIf, PrimSplitDeep, PrimNosplitDeep are []
-- (as they should be)

--run l | flattensToNothing l = return ([], [])
run l
  = case l of
        (IAps (ICon _ (ICPrim { primOp = PrimExpIf })) [] [e]) ->
          case e of
            (IAps (ICon _ (ICPrim { primOp = PrimIf }))
                 [ty_if] [cond, t_action, f_action]) | ty_if == itAction
              ->
               if (canLiftCond cond) then
                 map (prepend_branch (BranchIf cond True)) (run t_action) ++
                 map (prepend_branch (BranchIf cond False)) (run f_action)
               else run e

            (IAps (ICon _ (ICPrim { primOp = PrimCase }))
                 [ITNum idx_sz, elem_ty] (e_idx:e_dflt:ces))
                | elem_ty == itAction
              ->
               if (canLiftCond e_idx) then
                 let ce_pairs = makePairs ces
                     cs = map fst ce_pairs
                     doArm (e_cond, e_arm) n =
                         map (prepend_branch (BranchCase e_idx e_cond n idx_sz))
                             (run e_arm)
                     doDflt =
                         map (prepend_branch
                                  (BranchCaseDefault e_idx cs idx_sz))
                             (run e_dflt)
                 in  concat (zipWith doArm ce_pairs [0..]) ++
                     doDflt
               else run e

            (IAps (ICon i_sel (ICPrim { primOp = PrimArrayDynSelect }))
                 [elem_ty, ITNum idx_sz] [e_arr, e_idx]) ->
             if (canLiftCond e_idx) then
              case (expandRefs e_arr) of
                (IAps (ICon _ (ICPrim { primOp = PrimBuildArray }))
                     [elem_ty'] es_elems)
                  -> let sel_pos = getPosition i_sel
                         max_idx = (2^idx_sz) - 1
                         num_es = genericLength es_elems
                         -- funcs to make the branches
                         doElem e_elem n =
                             map (prepend_branch
                                      (BranchArrSel e_idx n idx_sz sel_pos))
                                 (run e_elem)
                         doOutOfBounds =
                             map (prepend_branch
                                      (BranchArrSelOutOfBounds
                                           e_idx num_es idx_sz sel_pos))
                                 (run icNoActions)
                         -- # of arms is the min of the elems and the max index
                         e_branches =
                             concat (zipWith doElem es_elems [0..max_idx])
                         dflt_branch =
                             if (max_idx > (num_es-1))
                             then doOutOfBounds
                             else []
                     in  e_branches ++ dflt_branch
                _ -> internalError ("ISplitIf run: unexpected array: " ++
                                    ppReadable e_arr)
             else run e

            _ -> internalError ("ISplitIf.run wrong kind of splitting.\n"
                                ++ (ppReadable l))

        (IAps (ICon _ (ICPrim { primOp = PrimJoinActions })) _ [e1,e2])
          -> do
                (a, x) <- run e1
                (b, y) <- run e2
                return (a ++ b, x ++ y)

        (IAps (ICon _ (ICPrim { primOp = op })) _ _)
          | isIfWrapper op
          -> internalError ("ISplitIf.run wrong kind of splitting.\n"
                            ++ (ppReadable l))

        (IAps function ty x)
          -> do y <- (mapM run x)
                return (concatMap fst y,
                        [IAps function ty (map (joinActions . snd) y)])

        _ -> return ([],[l])

push :: forall a . Bool -> IExpr a -> IExpr a
-- this function pushes SplitDeep and NosplitDeep down the tree
-- the "state" of whether we are in splitting mode or not is stored
-- and recursed down the tree in the argument do_split.  The initial
-- state of do_split is probably Flags.expandIf
push do_split e
  = let continue :: IExpr a -> IExpr a
        -- keeps pushing split or nosplit depending on the argument
        continue x = push do_split x
     in case e of
        (IAps j@(ICon _ (ICPrim { primOp = PrimJoinActions })) t [e1,e2])
          -> (IAps j t
               [continue e1,continue e2])
        (IAps   (ICon _ (ICPrim { primOp = PrimJoinActions })) _ _)
          -> internalError
               ("PrimJoinActions called with wrong number of arguments")

        (IAps wrap@(ICon _ (ICPrim { primOp = PrimExpIf })) [] [if_e]) ->
          -- leave as is, and continue in the arms
          case if_e of
            (IAps ic@(ICon _ (ICPrim { primOp = PrimIf }))
                 [ty_if] [cond, t_act, f_act]) | ty_if == itAction
              -> (IAps wrap []
                      [IAps ic [ty_if] [cond, continue t_act, continue f_act]])
            (IAps ic@(ICon _ (ICPrim { primOp = PrimCase }))
                 tys@[ITNum idx_sz, elem_ty] (e_idx:e_dflt:ces))
                | elem_ty == itAction
              -> let ces' = flattenPairs $ mapSnd continue $ makePairs ces
                     e_dflt' = continue e_dflt
                 in  (IAps wrap []
                          [IAps ic tys (e_idx:e_dflt':ces')])
            (IAps ic_sel@(ICon _ (ICPrim { primOp = PrimArrayDynSelect }))
                 sel_tys@[elem_ty, ITNum idx_sz] [e_arr, e_idx])
                | elem_ty == itAction
              -> case (expandRefs e_arr) of
                   (IAps ic_arr@(ICon _ (ICPrim { primOp = PrimBuildArray }))
                        [elem_ty'] es_elems)
                     -> let e_arr' = IAps ic_arr [elem_ty'] (map continue es_elems)
                        in  (IAps wrap []
                                 [IAps ic_sel sel_tys [e_arr', e_idx]])
                   _ -> internalError
                            ("ISplitIf push ExpIf: unexpected array: " ++
                             ppReadable e_arr)
            _ -> internalError
                      ("Bad argument to split annotation PrimExpIf: "++
                       ppReadable if_e)

        (IAps (ICon _ (ICPrim { primOp = PrimNoExpIf })) _ [if_e]) ->
          -- nosplit wrappers are removed, and continue in the arms
          case if_e of
            (IAps ic@(ICon _ (ICPrim { primOp = PrimIf }))
                 [ty_if] [cond, t_act, f_act]) | ty_if == itAction
              -> (IAps ic [ty_if] [cond, continue t_act, continue f_act])
            (IAps ic@(ICon _ (ICPrim { primOp = PrimCase }))
                 tys@[ITNum idx_sz, elem_ty] (e_idx:e_dflt:ces))
                | elem_ty == itAction
              -> let ces' = flattenPairs $ mapSnd continue $ makePairs ces
                     e_dflt' = continue e_dflt
                 in  (IAps ic tys (e_idx:e_dflt':ces'))
            (IAps ic_sel@(ICon _ (ICPrim { primOp = PrimArrayDynSelect }))
                 sel_tys@[elem_ty, ITNum idx_sz] [e_arr, e_idx])
                | elem_ty == itAction
              -> case (expandRefs e_arr) of
                   (IAps ic_arr@(ICon _ (ICPrim { primOp = PrimBuildArray }))
                        [elem_ty'] es_elems)
                     -> let e_arr' = IAps ic_arr [elem_ty'] (map continue es_elems)
                        in  (IAps ic_sel sel_tys [e_arr', e_idx])
                   _ -> internalError
                            ("ISplitIf: push NoExpIf: unexpected array: " ++
                             ppReadable e_arr)
            _ -> internalError
                      ("Bad argument to split annotation PrimNoExpIf: "++
                       ppReadable if_e)

        (IAps (ICon _ (ICPrim { primOp = PrimSplitDeep })) [] [e])
          -> push True e
        (IAps (ICon _ (ICPrim { primOp = PrimNosplitDeep })) [] [e])
          -> push False e

        (IAps (ICon _ (ICPrim { primOp = op })) _ _) | isIfWrapper op
          -> -- any other use an if-wrapper is invalid
             internalError ("Bad argument to split annotation "++
                            ppReadable e)

        -- a bare conditional: do what do_split says
        (IAps ic@(ICon _ (ICPrim { primOp = PrimIf }))
             [ty_if] [cond, t_act, f_act]) | ty_if == itAction
          -> if_annotate do_split
                 (IAps ic [ty_if] [cond, continue t_act, continue f_act])
        (IAps ic@(ICon _ (ICPrim { primOp = PrimCase }))
             tys@[ITNum idx_sz, elem_ty] (e_idx:e_dflt:ces))
            | elem_ty == itAction
          -> let ces' = flattenPairs $ mapSnd continue $ makePairs ces
                 e_dflt' = continue e_dflt
             in  if_annotate do_split (IAps ic tys (e_idx:e_dflt':ces'))
        (IAps ic_sel@(ICon _ (ICPrim { primOp = PrimArrayDynSelect }))
             sel_tys@[elem_ty, ITNum idx_sz] [e_arr, e_idx])
            | elem_ty == itAction
          -> case (expandRefs e_arr) of
               (IAps ic_arr@(ICon _ (ICPrim { primOp = PrimBuildArray }))
                    [elem_ty'] es_elems)
                 -> let e_arr' = IAps ic_arr [elem_ty'] (map continue es_elems)
                    in  if_annotate do_split
                            (IAps ic_sel sel_tys [e_arr', e_idx])
               _ -> internalError ("ISplitIf push bare: unexpected array: " ++
                                   ppReadable e_arr)

        -- if the IF is not an action, then the
        -- following fall-through is called
        (IAps f ts es) -> (IAps f ts (map continue es))
         -- XXX fixme: almost certainly we do not NEED to push it
         -- through an f, though there is no harm.

        _ -> e


if_annotate :: Bool -> IExpr a -> IExpr a
if_annotate do_split
  = let
        wrap_split if_expression
          = (IAps (ICon idPrimExpIf
                        (ICPrim { iConType = itAction `itFun` itAction,
                                  primOp = PrimExpIf }))
                  [] -- takes no type arguments
                  [if_expression])
     in case do_split of
           True -> wrap_split
           _    -> id

prepend_branch :: Branch_taken a ->
                  Path_through_actions a -> Path_through_actions a
prepend_branch br (brs, action) = ((br:brs), action)

-- XXX are these names OK? make then PreStrings?
make_branch_name :: Branch_taken a -> FString
make_branch_name (BranchIf _ True) = fs_T
make_branch_name (BranchIf _ False) = fs_F
make_branch_name (BranchArrSel _ n _ _) = mkFString ("_E" ++ show n)
make_branch_name (BranchArrSelOutOfBounds { }) = mkFString ("_OOB")
make_branch_name (BranchCase _ _ n _) = mkFString ("_A" ++ show n)
make_branch_name (BranchCaseDefault { }) = mkFString ("_DFL")

make_branch_cond :: Branch_taken a -> IExpr a
make_branch_cond (BranchIf c True) = c
make_branch_cond (BranchIf c False) = ieNot c
make_branch_cond (BranchArrSel e_idx n sz_idx pos_sel) =
    let ty_idx = itBitN sz_idx
        n_lit = iMkLitAt pos_sel ty_idx n
    in  iePrimEQ (ITNum sz_idx) e_idx n_lit
make_branch_cond (BranchArrSelOutOfBounds e_idx num_elems sz_idx pos_sel) =
    -- XXX construct "e_idx >= num_elems" instead?
    let ty_idx = itBitN sz_idx
        mkNEq n = let n_lit = iMkLitAt pos_sel ty_idx n
                  in  ieNot $ iePrimEQ (ITNum sz_idx) e_idx n_lit
    in  foldl ieAnd iTrue (map mkNEq [0..num_elems-1])
make_branch_cond (BranchCase e_idx e_arm sz_idx _) =
    iePrimEQ (ITNum sz_idx) e_idx e_arm
make_branch_cond (BranchCaseDefault e_idx es_arms sz_idx) =
    let mkNEq e_arm = ieNot $ iePrimEQ (ITNum sz_idx) e_idx e_arm
    in  foldl ieAnd iTrue (map mkNEq es_arms)

iExpandIfRule :: forall itype . Flags.Flags -> IRule itype ->
                 (SPIdSplitMap, [IRule itype])
iExpandIfRule flags
    r@(IRule { irule_name = i
             , irule_description = description
             , irule_pred = predicate
             , irule_body = action
             , irule_original = orig
             })
  = let
        paths :: [Path_through_actions itype]
        paths = run (push (Flags.expandIf flags) action)

        splitorig :: Maybe Id
        splitorig = maybe (Just i) Just orig

        mkRule :: Path_through_actions itype -> IRule itype
        mkRule (branches, action_list)
          = let
                fs_suffix :: FString
                fs_suffix = concatFString (map make_branch_name branches)

                -- potential name collision here XXX
                new_name :: Id
                new_name = mkSplitId i fs_suffix

                new_description :: String
                new_description = description ++ (getFString fs_suffix)

                terms :: [IExpr itype]
                terms = map make_branch_cond branches

                -- andOpt :: IExpr a -> IExpr a -> IExpr a
                -- andOpt x y = iTransBoolExpr flags (ieAnd x y)
                -- there is no obvious reason to choose
                -- foldl over foldr here
                new_predicate :: IExpr itype
                new_predicate = iTransBoolExpr flags (foldr ieAndOpt predicate terms)

                new_action :: IExpr itype
                new_action = joinActions action_list
             in
--trace ("mkRule " ++ new_description ++ (ppReadable branches) ++ " = " ++
--(ppReadable new_predicate) ++ " : " ++ (ppReadable action_list)) $
                r { irule_name = new_name
                  , irule_description = new_description
                  , irule_pred = new_predicate
                  , irule_body = new_action
                  , irule_original = splitorig
                  }

        mkSingleRule (_branches, action_list)
            = r { irule_body = joinActions action_list }
        new_rules :: [IRule itype]
        new_rules = case paths of
             [s] -> [mkSingleRule s]
             _   -> map mkRule paths

        sched = case paths of
             [_] -> []
             _   -> [(i,map getIRuleId new_rules)]

     in (sched , new_rules)


-- These return Nothing if the check was successful,
-- otherwise they return Just the offending expression.

check_if_wrappers :: (PrimOp -> Bool) -> IExpr itype -> Maybe (IExpr itype)
check_if_wrappers what_kind_of_if_wrapper e
  = case e of
         (IAps (ICon _ (ICPrim { primOp = op })) _ _)
           | (what_kind_of_if_wrapper op)
           -> Just e
         (IAps f _ es)
           -> (msum (map (check_if_wrappers what_kind_of_if_wrapper) (f:es)))
         _ -> Nothing

check_rules :: (PrimOp -> Bool) -> IRules a -> Maybe (IExpr a)
check_rules whatp (IRules _ rs) = msum $ map (check_rule whatp) rs

check_rule :: (PrimOp -> Bool) -> IRule a -> Maybe (IExpr a)
check_rule whatp r = check_if_wrappers whatp $ irule_body r

-- --------------------------

-- methods

iSplitIface :: Flags.Flags -> IEFace itype -> (SPIdSplitMap, IEFace itype)
iSplitIface flags ieface@(IEFace i xargs (Just (e,t)) Nothing wp fi)
    = if (t == itAction) then
            let irule = IRule i [] (getIdString i) wp iTrue e Nothing []
                irules = IRules [] [irule] -- no sps
            -- Don't call "optRules", since it only serves to remove rules!
            -- Methods should not be remove!  The one other function is to
            -- warn about never-ready methods, but AAddScheduleDefs does that
            -- for us, later.
            -- irules_opt <- optRules (iLiftThenExpandIfRules flags irules)
                (smap, irules_opt) = do_iExpandIfRules flags [] irules
            in (smap, IEFace i xargs Nothing (Just irules_opt) wp fi)
      else case e of
            (IAps (ICon av (ICTuple {fieldIds = [_val_id,_act_id]}))
                      [_] [val_,act_])
                | (av == idActionValue_)
                -> let irule = IRule i [] (getIdString i) wp iTrue act_ Nothing []
                       irules = IRules [] [irule] -- no sps
                       (smap, irules_opt) = do_iExpandIfRules flags [] irules
                    in (smap, IEFace i xargs (mkExpression val_ t)
                                       (Just irules_opt) wp fi)
            _ -> ([], ieface)

iSplitIface _ _ = internalError ("iSplitIface: no expression or unexpected rule")

mkExpression :: IExpr a -> IType -> Maybe (IExpr a, IType)
mkExpression val_ ty = if (isEmptyType (getAV_Type ty))
                       then Nothing
                       else (Just (val_,(getAV_Type ty)))


check_meth_rules :: (PrimOp -> Bool) -> IEFace a -> Maybe (IExpr a)
check_meth_rules whatp (IEFace _ _ _ (Just rs) _ _) = check_rules whatp rs
check_meth_rules _ _ = Nothing

-- --------------------------

-- XXX this inlinining is needed for array selection of actions
expandRefs :: IExpr a -> IExpr a
expandRefs (ICon _ (ICValue { iValDef = e })) = expandRefs e
expandRefs e = e

-- --------------------------

-- Check whether a condition can be lifted to a predicate.
-- If the condition contains a module argument or the result of
-- an ActionValue method call, then it cannot be lifted.
--
canLiftCond :: IExpr a -> Bool
-- conditions that can't be lifted
canLiftCond (IAps (ICon i (ICSel {})) _ _) | (i == idAVValue_) = False
canLiftCond (ICon _ (ICMethArg {})) = False
-- follow references
canLiftCond (ICon _ (ICValue { iValDef = e })) = canLiftCond e
-- recurse
canLiftCond (IAps f _ as) = canLiftCond f && all canLiftCond as
-- any other terminal is OK
canLiftCond (ICon {}) = True
-- all other expressions are unexpected after IExpand
canLiftCond e = internalError ("ISplitIf.canLiftCond: " ++ ppReadable e)

-- --------------------------

