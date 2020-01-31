module CFreeVars (
                  -- get the variables and value constructors:
                  getFVE,  -- of a CExpr
                  getFVDl, -- of a CDefl
                  getFVD,  -- of a CDef
                  getFVC,  -- of a CClause
                  getFVR,  -- of a CRule

                  -- for recursive constructs, allow removing it's own name
                  deleteV,

                  -- FVSet to list functions
                  fvSetToFreeVars,
                  fvSetToFreeCons,

                  -- get the variables bound by:
                  getPV,       -- a CPat
                  getPVs,      -- a CPat list
                  getStmtBind, -- a CStmt list
                  getLDefs,    -- a CDefl
                  getVQuals,   -- a [CQual]

                  -- get type constructors in:
                  getFQTyCons, -- a CQType
                  getFTyCons,  -- a CType
                  getFTCDn,    -- a CDefn
                  getFTCC,     -- a CClause

                  -- get type variables:
                  getFQTyVars,  -- returns the unique names
                  getFQTyVarsT, -- returns the unique TyVar (includes kind etc)
                  getCPTyVars,  -- like getFQTyVars but for CPred

                  -- get the names of toplevel CDefn
                  getVDefIds
   ) where

import qualified Data.Set as S
import Util(set_deleteMany)

import Id
import ErrorUtil(internalError)
import CSyntax
import PreIds(idPrimGetName)
import CType(typeclassId)
-- import PPrint
-- import Debug.Trace


-- --------------------

-- The "free variable" functions actually return free variables and
-- value constructors, which are not in the same namespace, so we return
-- two separate sets.

-- constructor set, variable set
type FVSet = (S.Set Id, S.Set Id)

fvSetToFreeVars :: FVSet -> [Id]
fvSetToFreeVars (_, v_set) = S.toList v_set

fvSetToFreeCons :: FVSet -> [Id]
fvSetToFreeCons (c_set, _) = S.toList c_set

emptyFVS :: FVSet
emptyFVS = (S.empty, S.empty)

unionFVS :: FVSet -> FVSet -> FVSet
unionFVS (cs1, vs1) (cs2, vs2) = (cs1 `S.union` cs2, vs1 `S.union` vs2)

unionManyFVS :: [FVSet] -> FVSet
unionManyFVS cvs =
    let (cs, vs) = unzip cvs
    in  (S.unions cs, S.unions vs)

-- delete a single bound variable
deleteV :: Id -> FVSet -> FVSet
deleteV i (cs, vs) = (cs, S.delete i vs)

-- delete many bound variables
deleteManyV :: [Id] -> FVSet -> FVSet
deleteManyV is (cs, vs) = (cs, set_deleteMany is vs)

-- delete a set of bound variables
minusVS :: FVSet -> S.Set Id -> FVSet
minusVS (cs, vs1) vs2 = (cs, vs1 `S.difference` vs2)

-- add a set of constructors
plusCS :: FVSet -> S.Set Id -> FVSet
plusCS (cs1, vs) cs2 = (cs1 `S.union` cs2, vs)

-- add a variable
addV :: Id -> FVSet -> FVSet
addV i (cs, vs) = (cs, S.insert i vs)

-- add a constructor
addC :: Id -> FVSet -> FVSet
addC i (cs, vs) = (S.insert i cs, vs)

-- singleton variable
singletonV :: Id -> FVSet
singletonV i = (S.empty, S.singleton i)

-- singleton variable
singletonC :: Id -> FVSet
singletonC i = (S.singleton i, S.empty)

-- --------------------

-- Get free value variables
getFVE :: CExpr -> FVSet
getFVE (CLam (Right i) e) = deleteV i (getFVE e)
getFVE (CLam (Left _) e) = getFVE e
getFVE (CLamT (Right i) _ e) = deleteV i (getFVE e)
getFVE (CLamT (Left _) _ e) = getFVE e
getFVE (Cletseq let_arms expr) =
    let (defs, free_vars_rhs) = getFVSeqDefls let_arms
        free_vars_expr = getFVE expr `minusVS` defs
    in  free_vars_rhs `unionFVS` free_vars_expr
getFVE (Cletrec defs expr) =
    let defined_vars = concatMap getLDefs defs
        fve_rhs_and_expr = unionManyFVS (getFVE expr : map getFVDl defs)
    in  deleteManyV defined_vars fve_rhs_and_expr
getFVE (CSelect e i) = getFVE e  ---- XXX WRONG i is field addV i (getFVE e)
getFVE (CSelectTT _ e i) = getFVE e -- XXX WRONG i is field addV i (getFVE e)
getFVE (CCon i es) = addC i (unionManyFVS (map getFVE es))
getFVE (Ccase pos e as) = unionFVS (getFVE e) (unionManyFVS (map getFVArm as))
  where getFVArm arm = 
            let -- better to do two minuses than union and one minus
                pat_bound  = getPV (cca_pattern arm)
                qual_bound = getVQuals (cca_filters arm)
            in (((getFVQuals (cca_filters arm)) `unionFVS`
                 (getFVE (cca_consequent arm) `minusVS` qual_bound)) `minusVS`
                 pat_bound) `plusCS` (getPC (cca_pattern arm))
getFVE (CStruct i ies) =
    -- XXX doesn't return the fields
    addC i $ unionManyFVS [getFVE e | (i, e) <- ies]
getFVE (CStructUpd e ies) =
    unionManyFVS (getFVE e : [getFVE e | (i, e) <- ies])
getFVE (Cwrite pos e v) = unionFVS (getFVE e) (getFVE v)
getFVE (CAny {}) = emptyFVS
getFVE (CVar i) = singletonV i
getFVE (CApply (CVar i) es) | i == idPrimGetName = singletonV idPrimGetName
getFVE (CApply e es) = unionManyFVS (map getFVE (e:es))
getFVE (CTaskApply e es) = unionManyFVS (map getFVE (e:es))
getFVE (CTaskApplyT e t es) = unionManyFVS (map getFVE (e:es))
getFVE (CLit _) = emptyFVS
getFVE (CBinOp l i r) =
    -- XXX should we be adding the operator?
    addV i (getFVE l `unionFVS` getFVE r)
getFVE (CHasType e t) = getFVE e
getFVE (Cif pos c t e) = getFVE c `unionFVS` getFVE t `unionFVS` getFVE e
getFVE (CSub pos e1 e2) = getFVE e1 `unionFVS` getFVE e2
getFVE (CSub2 e1 e2 e3) = getFVE e1 `unionFVS` getFVE e2 `unionFVS` getFVE e3
getFVE (CSubUpdate _ e_vec (e_h, e_l) e_rhs) = unionManyFVS $ map getFVE $ [e_vec, e_h, e_l, e_rhs]
getFVE (CCon1 _ i e) = addC i (getFVE e)
getFVE (Cmodule _ is) = getFVMStmts is
getFVE (Cinterface pos mi ds) =
    -- XXX mi is both a value constructor and a type constructor
    let defined_vars = concatMap getLDefs ds
        dfvs = deleteManyV defined_vars (unionManyFVS (map getFVDl ds))
    in  case mi of
          Nothing -> dfvs
          Just i -> addC i dfvs
getFVE (CmoduleVerilog e _ _ _ ses _ _ _) = unionManyFVS ([getFVE e] ++map (getFVE . snd) ses)
getFVE (CmoduleVerilogT _ e _ _ _ ses _ _ _) = unionManyFVS ([getFVE e] ++ map (getFVE . snd) ses)
getFVE (CForeignFuncC { }) = emptyFVS
getFVE (CForeignFuncCT { }) = emptyFVS
getFVE (Cdo _ ss) = getFVStmts ss
getFVE (Caction _ ss) = getFVStmts ss
getFVE (Crules _ rs) = unionManyFVS (map getFVR rs)
getFVE (CADump es) = unionManyFVS (map getFVE es)
getFVE (COper es) = unionManyFVS (map getFVO es)
getFVE (CTApply e _) = getFVE e
getFVE (CSelectT _ i) = emptyFVS ---- XXX WRONG i is field singletonV i
getFVE (CCon0 mi ci) = singletonC ci
getFVE (CConT _ i es) = addC i (unionManyFVS (map getFVE es))
getFVE (CStructT t ies) =
    -- XXX doesn't return the fields
    unionManyFVS [getFVE e | (i, e) <- ies]
getFVE (CLitT _ _) = emptyFVS
getFVE (CAnyT {}) = emptyFVS
getFVE (Cattributes _) = emptyFVS

-- Get the vars from a list of defls from letseq (not letrec).
-- Returns the bound def names (to be removed from the free vars of later
-- expressions or statements) and the free vars from those defs.
getFVSeqDefls :: [CDefl] -> (S.Set Id, FVSet)
getFVSeqDefls let_arms =
    let get_def_fve (defs_above, free_vars_above) let_arm =
            (defs_above `S.union` S.fromList (getLDefs let_arm),
             free_vars_above `unionFVS` (getFVDl let_arm `minusVS` defs_above))
    in  foldl get_def_fve (S.empty, emptyFVS) let_arms

getFVMStmts :: [CMStmt] -> FVSet
getFVMStmts ss =
    let -- takes the list of free variables from later statements,
        -- removes those bound by this statement, and
        -- adds the free variables of this statement
        getFVMStmt :: CMStmt -> FVSet -> FVSet
        getFVMStmt (CMStmt stmt) fvs = getFVStmt stmt fvs
        -- the rest don't bind any names, so just add free variables
        getFVMStmt (CMrules e) fvs = getFVE e `unionFVS` fvs
        getFVMStmt (CMinterface e) fvs = getFVE e `unionFVS` fvs
        getFVMStmt (CMTupleInterface _ es) fvs =
            unionManyFVS (map getFVE es) `unionFVS` fvs
    in  -- start from the bottom and work up
        foldr getFVMStmt emptyFVS ss

getFVStmts :: [CStmt] -> FVSet
getFVStmts ss =
    -- start from the bottom and work up
    foldr getFVStmt emptyFVS ss

-- takes the list of free variables from later statements,
-- removes those bound by this statement, and
-- adds the free variables of this statement
getFVStmt :: CStmt -> FVSet -> FVSet
getFVStmt (CSBindT p me _ _ e) s =
    ((getFVE e `plusCS` getPC p) `unionFVS` getMFVE me)
        `unionFVS` (s `minusVS` getPV p)
getFVStmt (CSBind p me _ e) s =
    ((getFVE e `plusCS` getPC p) `unionFVS` getMFVE me)
        `unionFVS` (s `minusVS` getPV p)
getFVStmt (CSletseq ds) s =
    let (defs, free_vars_rhs) = getFVSeqDefls ds
    in  free_vars_rhs `unionFVS` (s `minusVS` defs)
getFVStmt (CSletrec ds) s =
    unionManyFVS (map getFVDl ds) `unionFVS`
     (deleteManyV (concatMap getLDefs ds) s)
getFVStmt (CSExpr _ e) s = getFVE e `unionFVS` s

-- Get variables bound by a statement
getStmtBind (CSBindT p _ _ _ _) = S.toList (getPV p)
getStmtBind (CSBind p _ _ _) = S.toList (getPV p)
getStmtBind (CSletseq ds) = concatMap getLDefs ds
getStmtBind (CSletrec ds) = concatMap getLDefs ds
getStmtBind _ = []

{-
getMStmtBind (CMStmt s) = getStmtBind s
getMStmtBind _ = []
-}

getFVO (CRand e) = getFVE e
getFVO (CRator _ i) = singletonV i  -- XXX should we return operators?

-- Get type constructors
getFTCE :: CExpr -> S.Set Id
getFTCE (CLam _ e) = getFTCE e
getFTCE (CLamT _ t e) = getFTCE e `S.union` getFQTyCons t
getFTCE (Cletseq defs expr) = S.unions (getFTCE expr : map getFTCDl defs)
getFTCE (Cletrec ds e) = S.unions (getFTCE e : map getFTCDl ds)
getFTCE (CSelect e i) = getFTCE e
getFTCE (CSelectTT ti e fi) = S.insert ti (getFTCE e)
getFTCE (CCon i es) = S.unions (map getFTCE es)
getFTCE (Ccase pos e as) = S.union (getFTCE e) (S.unions (map getFTCArm as))
  where getFTCArm arm = getPT (cca_pattern arm) `S.union`
                        getFTCQuals (cca_filters arm) `S.union`
                        getFTCE (cca_consequent arm)
getFTCE (CStruct i ies) = S.unions [getFTCE e | (_, e) <- ies]
getFTCE (CStructUpd e ies) = S.unions (getFTCE e : [getFTCE e | (_, e) <- ies])
getFTCE (Cwrite pos e v) = S.union (getFTCE e) (getFTCE v)
getFTCE (CAny {}) = S.empty
getFTCE (CVar i) = S.empty
getFTCE (CApply e es) = S.unions (map getFTCE (e:es))
getFTCE (CTaskApply e es) = S.unions (map getFTCE (e:es))
getFTCE (CTaskApplyT e t es) =
    S.unions ([getFTyCons t] ++ map getFTCE (e:es))
getFTCE (CLit _) = S.empty
getFTCE (CBinOp l i r) = getFTCE l `S.union` getFTCE r
getFTCE (CHasType e t) = getFTCE e `S.union` getFQTyCons t
getFTCE (Cif pos c t e) = getFTCE c `S.union` getFTCE t `S.union` getFTCE e
getFTCE (CSub pos e1 e2) = getFTCE e1 `S.union` getFTCE e2
getFTCE (CSub2 e1 e2 e3) = getFTCE e1 `S.union` getFTCE e2 `S.union` getFTCE e3
getFTCE (CSubUpdate _ e_vec (e_h, e_l) e_rhs) = S.unions (map getFTCE [e_vec, e_h, e_l, e_rhs])
getFTCE (CCon1 ti ci e) = S.insert ti (getFTCE e)
getFTCE (Cmodule _ is) = S.unions (map getFTCMStmt is)
getFTCE (Cinterface pos mi ds) =
    -- XXX mi is both a value constructor and a type constructor
    let dcs = S.unions (map getFTCDl ds)
    in  case mi of
          Nothing -> dcs
          Just i  -> S.insert i dcs
getFTCE (CmoduleVerilog e _ _ _ ses _ _ _) =
    S.unions ([getFTCE e] ++ map (getFTCE . snd) ses)
getFTCE (CmoduleVerilogT t e _ _ _ ses _ _ _) =
    S.unions ([getFTyCons t, getFTCE e] ++ map (getFTCE . snd) ses)
getFTCE (CForeignFuncC _ t) = getFQTyCons t
getFTCE (CForeignFuncCT _ t) = getFTyCons t
getFTCE (Cdo _ ss) = S.unions (map getFTCStmt ss)
getFTCE (Caction _ ss) = S.unions (map getFTCStmt ss)
getFTCE (Crules _ rs) = S.unions (map getFTCR rs)
getFTCE (CADump es) = S.unions (map getFTCE es)
getFTCE (COper es) = S.unions (map getFTCO es)
getFTCE (CTApply e ts) = S.unions ([getFTCE e] ++ map getFTyCons ts)
getFTCE (CSelectT ti _) = S.singleton ti
getFTCE (CCon0 mi _) =
    case mi of
      Nothing -> S.empty
      Just i  -> S.singleton i
getFTCE (CConT ti _ es) = S.insert ti (S.unions (map getFTCE es))
getFTCE (CStructT t ies) =
    S.unions ([getFTyCons t] ++ [getFTCE e | (_, e) <- ies])
getFTCE (CLitT t _) = getFTyCons t
getFTCE (CAnyT _ _ t) = getFTyCons t
getFTCE (Cattributes _) = S.empty

-- since there is no worry about name binding, this can just be mapped over
-- the statement list (no folding involved)
getFTCStmt :: CStmt -> S.Set Id
getFTCStmt (CSBindT p me _ t e) =
    S.unions [getFQTyCons t, getPT p, getFTCE e, getMFTC me]
getFTCStmt (CSBind p me _ e) =
    S.unions [getPT p, getFTCE e, getMFTC me]
getFTCStmt (CSletseq ds) = S.unions (map getFTCDl ds)
getFTCStmt (CSletrec ds) = S.unions (map getFTCDl ds)
getFTCStmt (CSExpr _ e) = getFTCE e

getFTCMStmt :: CMStmt -> S.Set Id
getFTCMStmt (CMStmt s) = getFTCStmt s
getFTCMStmt (CMrules e) = getFTCE e
getFTCMStmt (CMinterface e) = getFTCE e
getFTCMStmt (CMTupleInterface _ es) = S.unions (map getFTCE es)

getFTCO (CRand e) = getFTCE e
getFTCO (CRator _ _) = S.empty

-- Get variables bound by a CDefl
getLDefs :: CDefl -> [Id]
getLDefs (CLValueSign d _) = [getDName d]
getLDefs (CLValue i _ _) = [i]
getLDefs (CLMatch p _) = S.toList (getPV p)

{-
getFVQuals :: [CQual] -> S.Set Id
getFVQuals qs = trace ("qs: " ++ ppReadable qs) $
                trace ("result: " ++ ppReadable (S.toList result)) $ result 
 where result = getFVQuals' qs
-}

getFVQuals :: [CQual] -> FVSet
getFVQuals [] = emptyFVS
getFVQuals (CQGen _ p e:qs) =
    (getFVE e `unionFVS` ((getFVQuals qs) `minusVS` (getPV p)))
        `plusCS` (getPC p)
getFVQuals (CQFilter e:qs) = getFVE e  `unionFVS`  getFVQuals qs

getVQuals :: [CQual] -> S.Set Id
getVQuals [] = S.empty
getVQuals (CQGen _ p e:qs) = getPV p `S.union` getVQuals qs
getVQuals (CQFilter e:qs) = getVQuals qs

-- Get variables bound in a pattern
getPV :: CPat -> S.Set Id
getPV (CPCon _ ps) = S.unions (map getPV ps)
getPV (CPstruct _ ips) = S.unions (map (getPV . snd) ips)
getPV (CPVar i) = S.singleton i
getPV (CPAs i p) = S.insert i (getPV p)
getPV (CPAny {}) = S.empty
getPV (CPLit _) = S.empty
getPV (CPMixedLit {}) = S.empty
getPV (CPCon1 _ _ p) = getPV p
getPV (CPConTs _ _ _ ps) = S.unions (map getPV ps)
getPV (CPOper _) = internalError "CFreeVars.getPV: CPOper"

-- Get (constructor and field) identifiers used in a pattern
getPC :: CPat -> S.Set Id
getPC (CPCon i ps) = S.insert i (S.unions (map getPC ps))
getPC (CPstruct i ips) =
    -- XXX we don't return fields
    S.insert i (S.unions [getPC p | (i, p) <- ips])
getPC (CPVar i) = S.empty
getPC (CPAs i p) = getPC p
getPC (CPAny {}) = S.empty
getPC (CPLit _) = S.empty
getPC (CPMixedLit {}) = S.empty
getPC (CPCon1 _ i p) = S.insert i (getPC p)
getPC (CPConTs _ i _ ps) = S.insert i (S.unions (map getPC ps))
getPC (CPOper ops) =
    let getPCO (CPRand p) = getPC p
        -- XXX we don't return operators
        getPCO (CPRator n i) = S.empty
    in  S.unions (map getPCO ops)

-- Get type constructors used in a pattern
getPT :: CPat -> S.Set Id
getPT (CPCon _ ps) = S.unions (map getPT ps)
getPT (CPstruct {}) = S.empty
getPT (CPVar {}) = S.empty
getPT (CPAs _ p) = getPT p
getPT (CPAny {}) = S.empty
getPT (CPLit {}) = S.empty
getPT (CPMixedLit {}) = S.empty
getPT (CPOper ops) = 
    let getPTO (CPRand p) = getPT p
        getPTO (CPRator n i) = S.empty
    in  S.unions (map getPTO ops)
getPT (CPCon1 ti _ _) = S.singleton ti
getPT (CPConTs ti _ ts ps) =
    S.insert ti (S.unions (map getFTyCons ts ++ map getPT ps))

getPTs ps = S.unions (map getPT ps)
getPCs ps = S.unions (map getPC ps)
getPVs ps = S.unions (map getPV ps)

-- Note that the def names themselves are included in the set.
-- To remove them, use "getLDefs".
getFVDl :: CDefl -> FVSet
getFVDl (CLValueSign def qs) =
        -- the "qs" are implicit condition for methods,
        -- so there is no binding there that can affect "def",
        -- thus we don't remove the variables bound there
	getFVQuals qs `unionFVS` getFVD def
getFVDl (CLValue _ cs qs) =
        -- as above, we don't subtract the vars bound in "qs"
	unionManyFVS (getFVQuals qs : map getFVC cs)
getFVDl (CLMatch p e) =
        -- here, we do want to remove any vars bound in the pattern
        getFVE e `minusVS` getPV p

-- Note that the def names themselves are included in the set.
-- To remove them, use "getDName".
getFVD :: CDef -> FVSet
getFVD (CDef _ _ cs)    = unionManyFVS (map getFVC cs)
getFVD (CDefT _ _ _ cs) = unionManyFVS (map getFVC cs)

getFVC :: CClause -> FVSet
getFVC (CClause ps qs e) =
	let bvs = getVQuals qs `S.union` getPVs ps
	in  ((getFVQuals qs `unionFVS` getFVE e) `minusVS` bvs) `plusCS` getPCs ps

getFVR :: CRule -> FVSet
getFVR (CRule _ n qs e) =
	let bvs = getVQuals qs
	in  getMFVE n `unionFVS` ((getFVQuals qs `unionFVS` getFVE e) `minusVS` bvs)
getFVR (CRuleNest _ n qs rs) =
	let bvs = getVQuals qs
	in  getMFVE n `unionFVS` ((getFVQuals qs `unionFVS` unionManyFVS (map getFVR rs)) `minusVS` bvs)

getMFVE :: Maybe CExpr -> FVSet
getMFVE Nothing = emptyFVS
getMFVE (Just e) = getFVE e

getFTCDl :: CDefl -> S.Set Id
getFTCDl (CLValueSign d me) = getFTCD d `S.union` getFTCQuals me
getFTCDl (CLValue _ cs me) =
    S.unions (map getFTCC cs) `S.union` getFTCQuals me
getFTCDl (CLMatch p e) = getPT p `S.union` getFTCE e

getFTCD :: CDef -> S.Set Id
getFTCD (CDef _ t cs) = S.unions (map getFTCC cs) `S.union` getFQTyCons t
getFTCD (CDefT _ _ t cs) = S.unions (map getFTCC cs) `S.union` getFQTyCons t

getFTCC :: CClause -> S.Set Id
getFTCC (CClause ps qs e) =
    getPTs ps `S.union` getFTCQuals qs `S.union` getFTCE e

getFTCR :: CRule -> S.Set Id
getFTCR (CRule _ n qs e) =
	getMFTC n `S.union` (getFTCQuals qs `S.union` getFTCE e)
getFTCR (CRuleNest _ n qs rs) =
	getMFTC n `S.union` (getFTCQuals qs `S.union` S.unions (map getFTCR rs))

getMFTC Nothing = S.empty
getMFTC (Just e) = getFTCE e

getFTCQuals :: [CQual] -> S.Set Id
getFTCQuals qs =
    -- since we don't worry about name binding, map is OK (instead of fold)
    let getFTCQual (CQGen t p e) =
            S.unions [getFTyCons t, getPT p, getFTCE e]
        getFTCQual (CQFilter e) = getFTCE e
    in  S.unions (map getFTCQual qs)

{-
getFVQTs :: CQType -> S.Set Id
getFVQTs t = set_deleteMany (getQTyVars t) (getFVQT t)

getQTyVars :: CQType -> [Id]
getQTyVars t = [ i | i <- S.toList (getFVQT t), getIdKind i == IKTyVar ]

getFVQT :: CQType -> S.Set Id
getFVQT (CQType ps t) = S.unions (getFVT t : map (\ (c, ts) -> S.insert c (S.unions (map getFVT ts))) ps)

getFVT :: CType -> S.Set Id
getFVT (TVar (TyVar i _ _)) = S.singleton i
getFVT (TCon (TyCon i _ _)) = S.singleton i
getFVT (TAp t t') = S.union (getFVT t) (getFVT t')
getFVT (TGen _ _) = S.empty
-}

getFQTyCons :: CQType -> S.Set Id
getFQTyCons (CQType ps t) = S.unions (getFTyCons t : map getCPTyCons ps)

getCPTyCons :: CPred -> S.Set Id
getCPTyCons (CPred (CTypeclass c) ts) = S.insert c (S.unions (map getFTyCons ts))

getFTyCons :: CType -> S.Set Id
getFTyCons (TVar (TyVar i _ _)) = S.empty
getFTyCons (TCon (TyCon i _ _)) = S.singleton i
getFTyCons (TCon (TyNum _ _)) = S.empty
getFTyCons (TAp t t') = S.union (getFTyCons t) (getFTyCons t')
getFTyCons (TGen _ _) = S.empty
getFTyCons (TDefMonad _) = S.empty  -- internalError "getFTyCons: TDefMonad"

getFQTyVars :: CQType -> S.Set Id
getFQTyVars (CQType ps t) = S.unions (getFTyVars t : map getCPTyVars ps)

getCPTyVars :: CPred -> S.Set Id
getCPTyVars (CPred c ts) = S.unions (map getFTyVars ts)

getFTyVars :: CType -> S.Set Id
getFTyVars (TVar (TyVar i _ _)) = S.singleton i
getFTyVars (TCon (TyCon i _ _)) = S.empty
getFTyVars (TCon (TyNum _ _)) = S.empty
getFTyVars (TAp t t') = S.union (getFTyVars t) (getFTyVars t')
getFTyVars (TGen _ _) = S.empty
getFTyVars (TDefMonad _) = S.empty  -- internalError "getFTyVars: TDefMonad"

-- I'm not completely sure that Eq over TyVars does the right
-- thing, that is, whether it is guaranteed that two identical
-- TyVars get folded (by S. unions) into one (as opposed to
-- some failing equality due to some different but insignificant
-- meta information on the TyVar)
getFQTyVarsT :: CQType -> S.Set TyVar
getFQTyVarsT (CQType ps t) = S.unions (getFTyVarsT t : map getCPTyVarsT ps)

getCPTyVarsT :: CPred -> S.Set TyVar
getCPTyVarsT (CPred c ts) = S.unions (map getFTyVarsT ts)

getFTyVarsT :: CType -> S.Set TyVar
getFTyVarsT (TVar i) = S.singleton i
getFTyVarsT (TCon (TyCon i _ _)) = S.empty
getFTyVarsT (TCon (TyNum _ _)) = S.empty
getFTyVarsT (TAp t t') = S.union (getFTyVarsT t) (getFTyVarsT t')
getFTyVarsT (TGen _ _) = S.empty
getFTyVarsT (TDefMonad _) = internalError "getFTyVars: TDefMonad"



-- Get Free TyCons
getFTCDn :: CDefn -> S.Set Id
getFTCDn (CValueSign d) = getFTCD d
getFTCDn (CValue _ cs) = S.unions (map getFTCC cs)
getFTCDn (Cprimitive _ t) = getFQTyCons t
getFTCDn (CprimType _) = S.empty
getFTCDn (CPragma _) = S.empty
getFTCDn (Cforeign { cforg_type = t } ) = getFQTyCons t
getFTCDn (Ctype _ _ t) = getFTyCons t
getFTCDn (Cdata { cd_internal_summands = summands,
                  cd_derivings = derivings }) =
    S.unions (map f summands) `S.union` S.fromList (map typeclassId derivings)
  where f summand = getFTyCons (cis_arg_type summand)
getFTCDn (Cstruct _ _ _ vs fields ds) =
    S.unions (map (getFQTyCons . cf_type) fields) `S.union` S.fromList (map typeclassId ds)
getFTCDn (Cclass _ ps _ _ _ fields) =
    S.unions (map getCPTyCons ps ++ map f fields)
  where f field = getFQTyCons (cf_type field) `S.union`
                  S.unions (map getFTCC (cf_default field))
                  -- XXX nothing with cf_orig_type?
getFTCDn (Cinstance qt ds) =
    S.union (getFQTyCons qt) (S.unions (map getFTCDl ds))
getFTCDn (CIinstance _ qt) = getFQTyCons qt
getFTCDn (CIValueSign _ t) = getFQTyCons t
getFTCDn (CItype i vs useposs) = S.empty
getFTCDn (CIclass incoh ps i vs fds useposs) = S.unions (map getCPTyCons ps)

getVDefIds :: CDefn -> [Id]
getVDefIds (CValueSign (CDef i _ _)) = [i]
getVDefIds (CValueSign (CDefT i _ _ _)) = [i]
getVDefIds (CValue i _) = [i]
getVDefIds (Cprimitive i _) = [i]
getVDefIds (CprimType i) = [iKName i]
getVDefIds (CPragma _) = []
getVDefIds (Cforeign { cforg_name = i }) = [i]
getVDefIds (Ctype i _ _) = [iKName i]
getVDefIds (Cdata { cd_name = name }) = [iKName name]
getVDefIds (Cstruct _ _ i _ _ _) = [iKName i]
getVDefIds (Cclass _ _ i _ _ _) = [iKName i]
getVDefIds (Cinstance _ _) = []
getVDefIds (CIinstance _ _) = []
getVDefIds (CItype i _ useposs) = [iKName i]
getVDefIds (CIclass _ _ i _ _ useposs) = [iKName i]
getVDefIds (CIValueSign i _) = [i]

