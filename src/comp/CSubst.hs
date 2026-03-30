module CSubst (
               CSEnv,
               CSubst(..),
               cSubstN,
               cSubstQualsN
              ) where

import CSyntax
import Util(mapSnd)
import Id(Id)
import CFreeVars (getPV, getLDefs)
import qualified Data.Map as M
import qualified Data.Set as S


-- --------------------

-- (type ctor qualifier map, value ctor qualifier, variable map, tyvar map)
type CSEnv = (M.Map Id Id, M.Map Id Id, M.Map Id CExpr, M.Map TyVar Type)

rmVarId :: CSEnv -> Id -> CSEnv
rmVarId (ctmap, cmap, vmap, vtmap) i = (ctmap, cmap, M.delete i vmap, vtmap)

rmVarIds :: CSEnv -> [Id] -> CSEnv
rmVarIds (ctmap, cmap, vmap, vtmap) is = (ctmap, cmap, foldr M.delete vmap is, vtmap)

-- --------------------

class CSubst a where
    cSubst :: CSEnv -> a -> a

cSubstN :: (CSubst a) => CSEnv -> a -> a
cSubstN r@(m1,m2,m3,m4) e =
    if (M.null m1 && M.null m2 && M.null m3 && M.null m4)
    then e
    else cSubst r e

instance (CSubst a) => CSubst [a] where
    cSubst r xs = map (cSubst r) xs

instance (CSubst a) => CSubst (Maybe a) where
    cSubst r Nothing = Nothing
    cSubst r (Just x) = Just (cSubst r x)

instance (CSubst a, CSubst b) => CSubst (a, b) where
    cSubst r (x, y) = (cSubst r x, cSubst r y)

cSubstConId :: CSEnv -> Id -> Id
cSubstConId (_,cmap,_,_) i = M.findWithDefault i i cmap

cSubstMConId :: CSEnv -> Maybe Id -> Maybe Id
cSubstMConId r (Just i) = Just (cSubstConId r i)
cSubstMConId r Nothing  = Nothing

cSubstTConId :: CSEnv -> Id -> Id
cSubstTConId (ctmap,_,_,_) i = M.findWithDefault i i ctmap

cSubstMTConId :: CSEnv -> Maybe Id -> Maybe Id
cSubstMTConId r (Just i) = Just (cSubstTConId r i)
cSubstMTConId r Nothing  = Nothing

cSubstTyVar :: CSEnv -> TyVar -> Type
cSubstTyVar (_,_,_,vtmap) v = M.findWithDefault (TVar v) v vtmap

instance CSubst CDefn where
    cSubst r (CValueSign d) = CValueSign (cSubst r d)
    cSubst r (CValue i cs) =
        -- remove the bound name
        let r' = rmVarId r i
        in  CValue i (cSubst r' cs)
    cSubst r d = d

instance CSubst CDef where
    cSubst r (CDefT i vs t cs) =
        let -- remove the bound name
            r' = rmVarId r i
        in  CDefT i vs (cSubst r t) (cSubst r' cs)
    cSubst r (CDef i t cs) =
        -- remove the bound name
        let r' = rmVarId r i
        in  CDef i (cSubst r t) (cSubst r' cs)

instance CSubst CClause where
    cSubst r (CClause ps qs e) =
        -- remove any bound pattern variables
        let pvars = concatMap getPatVars ps
            r' = rmVarIds r pvars
            (r'', qs') = cSubstQuals r' qs
        in  CClause (cSubst r ps) qs' (cSubst r'' e)

instance CSubst CRule where
    cSubst r (CRule rps mi qs e) =
        -- remove any bound pattern variablles
        let (r', qs') = cSubstQuals r qs
        in  CRule rps (cSubst r mi) qs' (cSubst r' e)
    cSubst r (CRuleNest rps mi qs rs) =
        -- remove any bound pattern variablles
        let (r', qs') = cSubstQuals r qs
        in  CRuleNest rps (cSubst r mi) qs' (cSubst r' rs)

cSubstQualsN :: CSEnv -> [CQual] -> [CQual]
cSubstQualsN env@(m1,m2,m3,m4) qs =
    if (M.null m1 && M.null m2 && M.null m3 && M.null m4)
    then qs
    else snd $ cSubstQuals env qs

cSubstQuals :: CSEnv -> [CQual] -> (CSEnv, [CQual])
cSubstQuals start_env old_qs =
    let cSubstQual (env, new_qs) (CQFilter e) =
            (env, (CQFilter (cSubst env e)) : new_qs)
        cSubstQual (env, new_qs) (CQGen t p e) =
            -- remove the bound pattern variables
            let pvars = getPatVars p
                env' = rmVarIds env pvars
                new_q = CQGen (cSubst env t) (cSubst env p) (cSubst env' e)
            in  (env', new_q:new_qs)
        (new_env, rev_new_qs) =
            foldl cSubstQual (start_env, []) old_qs
    in  (new_env, reverse rev_new_qs)

instance CSubst CExpr where
    cSubst r (CLam ei@(Right i) e) =
        -- remove the bound variable
        CLam ei (cSubst (rmVarId r i) e)
    cSubst r (CLam ei@(Left _) e) =
        CLam ei (cSubst r e)
    cSubst r (CLamT ei@(Right i) t e) =
        -- remove the bound variable
        CLamT ei (cSubst r t) (cSubst (rmVarId r i) e)
    cSubst r (CLamT ei@(Left _) t e) =
        CLamT ei (cSubst r t) (cSubst r e)
    cSubst r (Cletseq ds e) =
        let (r', ds') = cSubstSeqDefls r ds
        in  Cletseq ds' (cSubst r' e)
    cSubst r (Cletrec ds e) =
        -- remove all the bound def names from the the subst
        let vs = concatMap getDeflVars ds
            r' = rmVarIds r vs
        in  Cletrec (cSubst r' ds) (cSubst r' e)
    cSubst r (CSelect e i) =
        -- XXX should we be substituting field names?
        -- XXX getFVE does not return them
        CSelect (cSubst r e) i
    cSubst r (CCon i es) = CCon (cSubstConId r i) (cSubst r es)
    cSubst r (Ccase pos e arms) =
        let cSubstCaseArm (CCaseArm p qs e) =
                -- remove the bound variables
                let pvars = getPatVars p
                    r' = rmVarIds r pvars
                    (r'', qs') = cSubstQuals r' qs
                in  (CCaseArm (cSubst r p) qs' (cSubst r'' e))
        in  (Ccase pos (cSubst r e) (map cSubstCaseArm arms))
    cSubst r (CStruct mb i ies) =
        -- XXX should we be substituting field names?
        -- XXX getFVE does not return them
        CStruct mb (cSubstConId r i) (mapSnd (cSubst r) ies)
    cSubst r (CStructUpd e ies) =
        -- XXX should we be substituting field names?
        -- XXX getFVE does not return them
        CStructUpd (cSubst r e) (mapSnd (cSubst r) ies)
    cSubst r (Cwrite pos e1 e2) = (Cwrite pos (cSubst r e1) (cSubst r e2))
    cSubst r e@(CAny {}) = e
    cSubst (_,_,vmap,_) (CVar i) =
        -- use the variable map
        M.findWithDefault (CVar i) i vmap
    cSubst r (CApply f es) = CApply (cSubst r f) (cSubst r es)
    cSubst r (CTaskApply f es) = CTaskApply (cSubst r f) (cSubst r es)
    cSubst r (CTaskApplyT f t es) =
        CTaskApplyT (cSubst r f) (cSubst r t) (cSubst r es)
    cSubst r e@(CLit _) = e
    cSubst r (CBinOp e1 i e2) =
        -- XXX no substitution of operators?
        CBinOp (cSubst r e1) i (cSubst r e2)
    cSubst r (CHasType e t) = CHasType (cSubst r e) (cSubst r t)
    cSubst r (Cif pos e1 e2 e3) =
        Cif pos (cSubst r e1) (cSubst r e2) (cSubst r e3)
    cSubst r (CSub pos e1 e2) = CSub pos (cSubst r e1) (cSubst r e2)
    cSubst r (CSub2 e1 e2 e3) = CSub2 (cSubst r e1) (cSubst r e2) (cSubst r e3)
    cSubst r (CSubUpdate pos e_vec (e_h, e_l) e_rhs) =
        CSubUpdate pos (cSubst r e_vec) (cSubst r e_h, cSubst r e_l) (cSubst r e_rhs)
    cSubst r (Cmodule pos ss) = Cmodule pos (cSubstMStmts r ss)
    cSubst r (Cinterface pos i ds) =
        Cinterface pos (cSubstMConId r i) (cSubst r ds)
    cSubst r (CmoduleVerilog m ui cs rs ses fs sch ps) =
        CmoduleVerilog (cSubst r m) ui cs rs (mapSnd (cSubst r) ses) fs sch ps
    cSubst r (CForeignFuncC i t) = CForeignFuncC i (cSubst r t)
    cSubst r (Cdo b ss) = Cdo b (cSubstStmts r ss)
    cSubst r (Caction pos ss) = Caction pos (cSubstStmts r ss)
    cSubst r (Crules ps rs) = Crules ps (cSubst r rs)
    cSubst r (COper ops) = COper (cSubst r ops)
    cSubst r (CCon1 ti ci e) =
        CCon1 (cSubstTConId r ti) (cSubstConId r ci) (cSubst r e)
    cSubst r (CSelectTT ti e fi) =
        -- XXX should we be substituting field name?
        -- XXX getFVE does not return it
        CSelectTT (cSubstTConId r ti) (cSubst r e) fi
    cSubst r (CCon0 mi ci) = CCon0 (cSubstMTConId r mi) (cSubstConId r ci)
    cSubst r (CConT t i es) =
        CConT (cSubstTConId r t) (cSubstConId r i) (cSubst r es)
    cSubst r (CStructT t fs) =
        -- XXX should we be substituting field names?
        -- XXX getFVE does not return them
        CStructT (cSubst r t) (mapSnd (cSubst r) fs)
    cSubst r (CSelectT ti i) =
        -- XXX should we be substituting field name?
        -- XXX getFVE does not return it
        CSelectT (cSubstTConId r ti) i
    cSubst r (CLitT t l) = CLitT (cSubst r t) l
    cSubst r (CAnyT p uk t) = CAnyT p uk (cSubst r t)
    cSubst r (CmoduleVerilogT t m ui cs rs ses fs sch ps) =
        CmoduleVerilogT (cSubst r t) (cSubst r m) ui cs rs (mapSnd (cSubst r) ses) fs sch ps
    cSubst r (CForeignFuncCT i t) = (CForeignFuncCT i (cSubst r t))
    cSubst r (CTApply e ts) = CTApply (cSubst r e) (cSubst r ts)
    cSubst r e@(Cattributes {}) = e


cSubstSeqDefls :: CSEnv -> [CDefl] -> (CSEnv, [CDefl])
cSubstSeqDefls r ds =
    -- each def should have the previous defs removed from the subst
    -- and the final subst (with all defs removed) is used on "e"
    let cSubstSeq (env, new_ds) d =
            let vs = getDeflVars d
                new_env = rmVarIds env vs
            in  (new_env, (cSubst env d):new_ds)
        (r', rev_ds') = foldl cSubstSeq (r, []) ds
    in  (r', reverse rev_ds')

instance CSubst CDefl where
    cSubst r (CLValueSign d me) =
        CLValueSign (cSubst r d) (snd (cSubstQuals r me))
    cSubst r (CLValue i cs me) =
        -- remove the bound name
        let r' = rmVarId r i
        in  CLValue i (cSubst r' cs) (snd (cSubstQuals r me))
    cSubst r (CLMatch p e) =
        -- remove the bound name
        let pvars = getPatVars p
            r' = rmVarIds r pvars
        in  CLMatch (cSubst r p) (cSubst r' e)

instance CSubst CQType where
    cSubst r (CQType preds t) = CQType (cSubst r preds) (cSubst r t)

instance CSubst CPred where
    cSubst r (CPred (CTypeclass cls) ts) =
        CPred (CTypeclass (cSubstTConId r cls)) (map (cSubst r) ts)

instance CSubst Type where
    cSubst r (TVar v) = cSubstTyVar r v
    cSubst r (TCon (TyCon i k s)) = TCon (TyCon (cSubstTConId r i) k s)
    cSubst r t@(TCon (TyNum {})) = t
    cSubst r t@(TCon (TyStr {})) = t
    cSubst r (TAp t1 t2) = TAp (cSubst r t1) (cSubst r t2)
    cSubst r t@(TGen {}) = t
    cSubst r t@(TDefMonad {}) = t

instance CSubst CPat where
    cSubst r (CPCon i ps) = CPCon (cSubstConId r i) (map (cSubst r) ps)
    cSubst r (CPstruct mb i ips) =
        -- XXX should we be substituting field names?
        -- XXX getFVE does return them, in this case
        CPstruct mb (cSubstConId r i) (mapSnd (cSubst r) ips)
    cSubst r p@(CPVar {}) = p
    cSubst r (CPAs i p) = CPAs i (cSubst r p)
    cSubst r p@(CPAny {}) = p
    cSubst r p@(CPLit {}) = p
    cSubst r p@(CPMixedLit {}) = p
    cSubst r (CPOper ops) =
        let cSubstOp (CPRand p) = CPRand (cSubst r p)
            -- XXX no substitution of operators?
            cSubstOp (CPRator n i) = CPRator n i
        in  CPOper (map cSubstOp ops)
    cSubst r (CPCon1 ti ci p) =
        CPCon1 (cSubstTConId r ti) (cSubstConId r ci) (cSubst r p)
    cSubst r (CPConTs ti ci ts ps) =
        CPConTs (cSubstTConId r ti) (cSubstConId r ci)
            (cSubst r ts) (cSubst r ps)

-- because statements define names which need to be removed from the
-- environments of later statements, we have to fold over the statements,
-- and can't just map a CSubst instance onto them
cSubstStmts :: CSEnv -> [CStmt] -> [CStmt]
cSubstStmts start_env old_ss =
    let fn (env, new_ss) old_s =
            let (env', new_s) = cSubstStmt env old_s
            in  (env', new_s:new_ss)
        rev_new_ss = snd $ foldl fn (start_env, []) old_ss
    in  reverse rev_new_ss

cSubstStmt :: CSEnv -> CStmt -> (CSEnv, CStmt)
cSubstStmt env (CSBindT p me pps t e) =
    -- remove any bound pattern variables
    let pvars = getPatVars p
        env' = rmVarIds env pvars
        new_s = CSBindT (cSubst env p) (cSubst env me) pps (cSubst env t) (cSubst env e)
    in  (env', new_s)
cSubstStmt env (CSBind p me pps e) =
    -- remove any bound pattern variables
    let pvars = getPatVars p
        env' = rmVarIds env pvars
        new_s = CSBind (cSubst env p) (cSubst env me) pps (cSubst env e)
    in  (env', new_s)
cSubstStmt env (CSletseq ds) =
    let (env', ds') = cSubstSeqDefls env ds
        new_s = CSletseq ds'
    in  (env', new_s)
cSubstStmt env (CSletrec ds) =
    -- remove all the bound def names from the the subst
    let vs = concatMap getDeflVars ds
        env' = rmVarIds env vs
        new_s = CSletrec (map (cSubst env) ds)
    in  (env', new_s)
cSubstStmt env (CSExpr me e) =
    let new_s = CSExpr me (cSubst env e)
    in  (env, new_s)

-- because statements define names which need to be removed from the
-- environments of later statements, we have to fold over the statements,
-- and can't just map a CSubst instance onto them
cSubstMStmts :: CSEnv -> [CMStmt] -> [CMStmt]
cSubstMStmts start_env old_ss =
    let cSubstMStmt (env, new_ss) (CMStmt s) =
            let (env', new_s) = cSubstStmt env s
            in  (env', (CMStmt new_s):new_ss)
        cSubstMStmt (env, new_ss) (CMrules e) =
            let new_s = CMrules (cSubst env e)
            in  (env, new_s:new_ss)
        cSubstMStmt (env, new_ss) (CMinterface e) =
            let new_s = CMinterface (cSubst env e)
            in  (env, new_s:new_ss)
        cSubstMStmt (env, new_ss) (CMTupleInterface pos es) =
            let new_s = CMTupleInterface pos (map (cSubst env) es)
            in  (env, new_s:new_ss)
        (rev_new_ss) =
            snd $ foldl cSubstMStmt (start_env, []) old_ss
    in  reverse rev_new_ss

instance CSubst COp where
    cSubst r (CRand e) = CRand (cSubst r e)
    -- XXX no substitution of operators?
    cSubst r (CRator n i) = CRator n i


-- --------------------

getDeflVars :: CDefl -> [Id]
getDeflVars d = getLDefs d

getPatVars :: CPat -> [Id]
getPatVars = S.toList . getPV

-- --------------------
