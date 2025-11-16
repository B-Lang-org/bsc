module CtxRed(cCtxReduceDef, cCtxReduceIO, CtxRed(..)) where

import Data.List(partition, (\\))
import Control.Monad(when)
import PFPrint
import Id
import PreIds(tmpTyVarIds)
import Error(internalError, EMsg, ErrorHandle, bsWarning, bsError)
import Flags(Flags)
import CSyntax
import Type
import CType(getTyVarId, isGeneratedTVar, tVar, tVarKind)
import Subst
import Pred
import TIMonad
import TCMisc
import SymTab
import MakeSymTab(convCQTypeWithAssumps)
import VModInfo(VArgInfo(..))
import Util(concatMapM)

import Debug.Trace(traceM)
import IOUtil(progArgs)

doTraceCtxReduce :: Bool
doTraceCtxReduce = "-trace-ctxreduce" `elem` progArgs

cCtxReduceIO :: ErrorHandle -> Flags -> SymTab -> CPackage -> IO CPackage
cCtxReduceIO errh flags s (CPackage mi exps imps impsigs fixs ds includes) = do
    -- The False argument to 'runTI' indicates that incoherent instances should not be matched at this time
    -- We want to preserve those contexts to be handled in typecheck (XXX why?)
    let (res, wmsgs) = runTI flags False s (mapM ctxRed ds)
    when (not (null wmsgs)) $ bsWarning errh wmsgs
    case res of
      Left emsgs -> bsError errh emsgs
      Right ds' -> return (CPackage mi exps imps impsigs fixs ds' includes)

cCtxReduceDef :: Flags -> SymTab -> CDefn -> Either [EMsg] CDefn
cCtxReduceDef flags s def =
    -- XXX This assumes no warnings in the Left case!  If we want to handle errors and
    -- warnings better, return an ErrorMonad.
    -- The False argument to 'runTI' indicates that incoherent instances should not be matched at this time
    -- We want to preserve those contexts to be handled in typecheck (XXX why?)
    case fst (runTI flags False s (ctxRed def)) of
    Left msgs -> Left msgs
    Right t   -> Right t

class CtxRed a where
    ctxRed :: a -> TI a

instance CtxRed CField where
    ctxRed field = do
      (_, cqt') <- ctxRedCQType (cf_type field)
      def' <- mapM ctxRed (cf_default field)
      popBoundTVs  -- necessary after call to ctxRedCQType
                   -- bound vars should be in scope for the defaults
      return (field { cf_type = cqt',
                      cf_default = def'
                    })

instance CtxRed CDefn where
    ctxRed (CValueSign d) = do
        d' <- ctxRed d
        return (CValueSign d')

-- primitives should be defined so they don't need ctxRed
{-
    ctxRed (Cprimitive i cqt) = do
        (_, cqt') <- ctxRedCQType cqt
        popBoundTVs  -- necessary after call to ctxRedCQType
        return (Cprimitive i cqt')
-}
    -- XXX do data&class?

    ctxRed (Cstruct vis ss idk vs fs ds) = do
        fs' <- mapM ctxRed fs
        return (Cstruct vis ss idk vs fs' ds)

    ctxRed (Cinstance cqt ds) = do
        (s, cqt') <- ctxRedInstHead cqt
        ds' <- ctxRed (apSub s ds)
        popBoundTVs  -- necessary after call to ctxRedCQType
                     -- but only after we've recursed into the defs
        return (Cinstance cqt' ds')

    ctxRed f@(Cforeign {}) = do
        (_, cqt') <- ctxRedCQType (cforg_type f)
        popBoundTVs  -- necessary after call to ctxRedCQType
        return (f { cforg_type = cqt' })

    ctxRed d@(Cclass incoh cpreds ik vs fds fs) = do
       -- get any kind information we have for the type parameters
       -- XXX is this necessary?
       let i = iKName ik
           ts = map TVar (getVarKinds ik vs)
           c = TCon (TyCon i Nothing TIabstract)
           ct = cTApplys c ts
       -- start a scope for this class
       (_, CQType _ ct') <- ctxRedCQType (CQType [] ct)
       -- convert the fields
       -- (fields can have default exprs, and all expr code to be typechecked
       -- needs to have ctxRed applied to it)
       fs' <- mapM ctxRed fs
       -- pop the scope added by ctxRedCQType
       popBoundTVs
       -- XXX update the kind of the class with what we learned?
{-
       let mk' = case (leftTyCon ct') of
                   Nothing -> Nothing
                   Just c' -> tcon_kind c'
           ik' = case mk' of
                   Nothing -> ik
                   Just k' -> IdKind i k'
-}
       return (Cclass incoh cpreds ik vs fds fs')

    ctxRed d = return d

instance CtxRed CDefl where
    ctxRed (CLValueSign d me) = do
        d' <- ctxRed d
        me' <- ctxRed me
        return (CLValueSign d' me')
    ctxRed (CLValue i cs me) = do
        cs' <- ctxRed cs
        me' <- ctxRed me
        return (CLValue i cs' me')
    ctxRed (CLMatch p e) = do
        p' <- ctxRed p
        e' <- ctxRed e
        return (CLMatch p' e')

instance CtxRed CDef where
    ctxRed (CDef i cqt cs) = do
        (s, cqt') <- ctxRedCQType cqt
        cs' <- ctxRed (apSub s cs)
        popBoundTVs  -- necessary after call to ctxRedCQType
                     -- but only after we've recursed into the defs
        return (CDef i cqt' cs')
    ctxRed _ = internalError "TypeCheck instance CtxRed CDef"

instance CtxRed CClause where
    ctxRed (CClause ps qs e) = do
        qs' <- ctxRed qs
        e' <- ctxRed e
        return (CClause ps qs' e')

instance CtxRed CExpr where
    ctxRed (CLam i e) = do
        e' <- ctxRed e
        return (CLam i e')
    ctxRed (CLamT i qt e) = do
        -- CLamT does not bind type variable names, so we don't need to
        -- reduce "e" between "ctxRedCQType" and popping the bound tvs
        e' <- ctxRed e
        (_, qt') <- ctxRedCQType qt
        popBoundTVs  -- necessary after call to ctxRedCQType
        return (CLamT i qt' e')
    ctxRed (Cletseq ds e) = do
        ds' <- ctxRed ds
        e' <- ctxRed e
        return (Cletseq ds' e')
    ctxRed (Cletrec ds e) = do
        ds' <- ctxRed ds
        e' <- ctxRed e
        return (Cletrec ds' e')
    ctxRed (CSelect e i) = do
        e' <- ctxRed e
        return (CSelect e' i)
    ctxRed (CSelectTT ti e i) = do
        e' <- ctxRed e
        return (CSelectTT ti e' i)
    ctxRed (CCon i es) = do
        es' <- ctxRed es
        return (CCon i es')
    ctxRed (Ccase pos e as) = do
        e' <- ctxRed e
        as' <- ctxRed as
        return (Ccase pos e' as')
    ctxRed (CStruct mb i ies) = do
        ies' <- ctxRed ies
        return (CStruct mb i ies')
    ctxRed (CStructUpd e ies) = do
        e' <- ctxRed e
        ies' <- ctxRed ies
        return (CStructUpd e' ies')
    ctxRed (Cwrite pos e v) = do
        e' <- ctxRed e
        v' <- ctxRed v
        return (Cwrite pos e' v')
    ctxRed e@(CAny {}) = return e
    ctxRed e@(CVar _) = return e
    ctxRed (CApply e es) = do
        e' <- ctxRed e
        es' <- ctxRed es
        return (CApply e' es')
    ctxRed (CTaskApply e es) = do
        e' <- ctxRed e
        es' <- ctxRed es
        return (CTaskApply e' es')
    ctxRed e@(CLit _) = return e
    ctxRed (CBinOp e1 o e2) = do
        e1' <- ctxRed e1
        e2' <- ctxRed e2
        return (CBinOp e1' o e2')
    ctxRed (CHasType e cqt) = do
        -- CHasType does not bind type variable names, so we don't need to
        -- reduce "e" between "ctxRedCQType" and popping the bound tvs
        e' <- ctxRed e
        (_, cqt') <- ctxRedCQType cqt
        popBoundTVs  -- necessary after call to ctxRedCQType
        return (CHasType e' cqt')
    ctxRed (Cif pos e1 e2 e3) = do
        e1' <- ctxRed e1
        e2' <- ctxRed e2
        e3' <- ctxRed e3
        return (Cif pos e1' e2' e3')
    ctxRed (CSub pos e1 e2) = do
        e1' <- ctxRed e1
        e2' <- ctxRed e2
        return (CSub pos e1' e2')
    ctxRed (CSub2 e1 e2 e3) = do
        e1' <- ctxRed e1
        e2' <- ctxRed e2
        e3' <- ctxRed e3
        return (CSub2 e1' e2' e3')
    ctxRed (CSubUpdate pos e_vec (e_h, e_l) e_rhs) = do
        e_vec' <- ctxRed e_vec
        e_h'   <- ctxRed e_h
        e_l'   <- ctxRed e_l
        e_rhs' <- ctxRed e_rhs
        return (CSubUpdate pos e_vec' (e_h', e_l') e_rhs')
    ctxRed (CCon1 ti i e) = do
        e' <- ctxRed e
        return (CCon1 ti i e')
    ctxRed (Cmodule pos is) = do
        is' <- ctxRed is
        return (Cmodule pos is')
    ctxRed (Cinterface pos mi ds) = do
        ds' <- ctxRed ds
        return (Cinterface pos mi ds')
    ctxRed (CmoduleVerilog m ui c r ses fs sch ps) = do
        m' <- ctxRed m
        ses' <- ctxRed ses
        return (CmoduleVerilog m' ui c r ses' fs sch ps)
    -- the contexts on the cqt here are not a real type,
    -- but are extra info for better error reporting in tiExpr
    ctxRed e@(CForeignFuncC i cqt) = return e
    ctxRed (Cdo r ss) = do
        ss' <- ctxRed ss
        return (Cdo r ss')
    ctxRed (Caction pos ss) = do
        ss' <- ctxRed ss
        return (Caction pos ss')
    ctxRed (Crules ps rs) = do
        rs' <- ctxRed rs
        return (Crules ps rs')
    ctxRed (CConT ti i es) = do
        es' <- ctxRed es
        return (CConT ti i es')
    ctxRed e@(Cattributes _) = return e
    ctxRed e = internalError ("ctxRed: " ++ ppReadable e)

instance CtxRed Char where
    ctxRed c = return c

instance CtxRed CStmt where
    ctxRed (CSBindT p name pprops qt e) = do
        -- CSBindT does not bind type variable names, so we don't need to
        -- reduce "e" between "ctxRedCQType" and popping the bound tvs
        p' <- ctxRed p
        e' <- ctxRed e
        (_, qt') <- ctxRedCQType qt
        popBoundTVs  -- necessary after call to ctxRedCQType
        return (CSBindT p name pprops qt' e')
    ctxRed (CSBind p name pprops e) = do
        p' <- ctxRed p
        e' <- ctxRed e
        return (CSBind p name pprops e')
    ctxRed (CSletseq ds) = do
        ds' <- ctxRed ds
        return (CSletseq ds')
    ctxRed (CSletrec ds) = do
        ds' <- ctxRed ds
        return (CSletrec ds')
    ctxRed (CSExpr name e) = do
        e' <- ctxRed e
        return (CSExpr name e')

instance CtxRed CMStmt where
    ctxRed (CMStmt s) = do
        s' <- ctxRed s
        return (CMStmt s')
    ctxRed (CMrules e) = do
        e' <- ctxRed e
        return (CMrules e')
    ctxRed (CMinterface e) = do
        e' <- ctxRed e
        return (CMinterface e')
    ctxRed (CMTupleInterface pos es) = do
        es' <- mapM ctxRed es
        return (CMTupleInterface pos es')

instance CtxRed CQual where
    ctxRed (CQGen t p e) = do
        e' <- ctxRed e
        return (CQGen t p e')
    ctxRed (CQFilter e) = do
        e' <- ctxRed e
        return (CQFilter e')

instance CtxRed CRule where
    ctxRed (CRule rps mi qs e) = do
        mi' <- ctxRed mi
        qs' <- ctxRed qs
        e' <- ctxRed e
        return (CRule rps mi' qs' e')
    ctxRed (CRuleNest rps mi qs rs) = do
        mi' <- ctxRed mi
        qs' <- ctxRed qs
        rs' <- ctxRed rs
        return (CRuleNest rps mi' qs' rs')

instance (CtxRed a) => CtxRed [a] where
    ctxRed xs = mapM ctxRed xs

instance (CtxRed a, CtxRed b) => CtxRed (a, b) where
    ctxRed (a, b) = do
        a' <- ctxRed a
        b' <- ctxRed b
        return (a', b')

instance (CtxRed a, CtxRed b, CtxRed c) => CtxRed (a, b, c) where
    ctxRed (a, b, c) = do
        a' <- ctxRed a
        b' <- ctxRed b
        c' <- ctxRed c
        return (a', b', c')

instance (CtxRed a) => CtxRed (Maybe a) where
    ctxRed Nothing = return Nothing
    ctxRed (Just e) = do e' <- ctxRed e; return (Just e')

instance CtxRed CCaseArm where
    ctxRed arm = do reduced_filters <- ctxRed (cca_filters arm)
                    reduced_consequent <- ctxRed (cca_consequent arm)
                    return (arm { cca_filters = reduced_filters,
                                  cca_consequent = reduced_consequent })

-- for convenience
instance CtxRed Id where
    ctxRed i = return i
instance CtxRed CPat where
    ctxRed p = return p
instance CtxRed VArgInfo where
    ctxRed a = return a

-- A separate entry point into ctxRedCQType for instance heads
-- (to avoid synonym-expansion and SizeOf issues without unduly
-- disturbing non-instance types)
ctxRedInstHead :: CQType -> TI (Subst, CQType)
ctxRedInstHead = ctxRedCQType' True

ctxRedCQType :: CQType -> TI (Subst, CQType)
ctxRedCQType = ctxRedCQType' False

ctxRedCQType' :: Bool -> CQType -> TI (Subst, CQType)
ctxRedCQType' isInstHead cqt = do

    -- find out what variables were bound prior to here
    prev_bound_tvs <- getBoundTVs

    -- make a table of assumptions about the kinds of those bound vars
    let btks = [ (getTyVarId tv, kind tv) | tv <- prev_bound_tvs ]

    -- convert the CQType (using the assumptions we know)
    sy <- getSymTab
    (qs0 :=> t0) <- case convCQTypeWithAssumps sy btks cqt of
                     Left emsg -> err emsg
                     Right qt -> return qt

    -- do extra reduction on instance heads to avoid synonym-expansion
    -- and SizeOf issues, without unduly disturbing non-instance types
    -- (and do it here, after "convCQType", so that "expPrimTCons" sees
    -- the qualified types)
    (qs, t) <- if isInstHead
               then do -- XXX disable expanding of type synonyms until
                       -- XXX failures with TLM instances are resolved
                       -- XXX (vqs_extra, t1) <- expPrimTCons t0 (expandSyn t0)
                       (vqs_extra, t1) <- expPrimTCons t0
                       let qs_extra = map toPredWithPositions vqs_extra
                       return (qs0 ++ qs_extra, t1)
               else return (qs0, t0)

    -- construct the predicates and try to reduce them
    vqs <- concatMapM (mkVPred (getPosition cqt)) qs

    -- create a type variable for trimming later
    (trim_point, _) <- newTVarId "ctxRedCQType" KStar cqt

    -- core context reduction
    let dvs = (tv vqs) ++ prev_bound_tvs
    (ps, _, s) <- reducePredsAggressive (Just dvs) [] vqs

    let t' = apSub s t

    -- don't bind any generated type variables introduced by the type-checker
    -- (to avoid possible variable capture in typecheck)
    let (bad_vars, good_vars) = partition isGeneratedTVar (tv (ps, t'))
    let used_vars = good_vars ++ prev_bound_tvs
    let safe_tyvar_ids = [ v | v <- tmpTyVarIds, tVar v `notElem` used_vars ]

    -- we don't need to pass this along, because these generated vars
    -- should only appear in ps and t' (any the trimmed part of s)
    let s' = mkSubst [(bad_var, TVar safe_var) | (bad_var, safe_id) <- zip bad_vars safe_tyvar_ids,
                                                 let safe_var = tVarKind safe_id (kind bad_var) ]
    let ps' = apSub s' ps
    let t'' = apSub s' t'
    -- because of NumAlias and pseudo-constructors like SizeOf that expand into
    -- new types, some vars from s' could appear in the RHS of s,
    -- so we need to apply s' to s
    let s_final = trimSubst trim_point (apSubstToSubst s' s)

    -- push the set of tyvars bound at this level (with their inferred kinds)
    let bvs = (tv (ps',t'')) \\ prev_bound_tvs
    addBoundTVs bvs
    let cqt' = CQType (map (predToCPred . toPred) ps') t''

    when doTraceCtxReduce $ do
       traceM ("ctxRedCQType\n")
       traceM ("cqt: " ++ ppReadable cqt)
       traceM ("ps: " ++ ppReadable ps)
       traceM ("s: " ++ ppReadable s)
       traceM ("t' :" ++ ppReadable t')
       -- t'' and ps' are in cqt'
       traceM ("s_final: " ++ ppReadable s_final)
       traceM ("cqt': " ++ ppReadable cqt')

    -- It is up to the callers of this function to pop the bound tvs
    -- at the appropriate point: either immediately, if vars are not bound
    -- or after recursing into subexpressions, if vars are bound.
    --popBoundTVs
    return (s_final, cqt')


getVarKinds :: IdK -> [Id] -> [TyVar]
getVarKinds (IdK _) vs = map tVar vs
getVarKinds (IdKind _ k) vs =
{-
    let ks = getArgKinds k
    in  zipWith tVarKind vs ks
-}
    let mkArgKinds [] _ = []
        mkArgKinds (i:is) (Kfun a b) =
            tVarKind i a : mkArgKinds is b
        -- XXX if the length doesn't match?
        mkArgKinds is _ = map tVar is
    in
        mkArgKinds vs k
getVarKinds (IdPKind _ pk) vs =
    let mkArgKinds [] _ = []
        mkArgKinds (i:is) (PKfun a b) =
            mkKind i a : mkArgKinds is b
        -- XXX if the length doesn't match?
        mkArgKinds is _ = map tVar is

        mkKind i pk = case (getKind pk) of
                        Just k -> tVarKind i k
                        Nothing -> tVar i

        getKind PKNoInfo = Nothing
        getKind PKStar = Just KStar
        getKind PKNum = Just KNum
        getKind PKStr = Just KStr
        getKind (PKfun a b) =
            case (getKind a, getKind b) of
              (Just ak, Just bk) -> Just $ Kfun ak bk
              _ -> Nothing
    in
        mkArgKinds vs pk
