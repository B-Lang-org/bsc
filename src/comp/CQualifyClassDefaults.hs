module CQualifyClassDefaults (
        ClassDefaultQualEnv(..),
        qualifyClassDefaultClauses
    ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Changed(Changed(..), changed2, changedOr)
import CFreeVars(getLDefs, getPV)
import CSyntax
import Id(Id)
import Util(mapSnd)


-- The three namespaces which can contain free names in a class default.
-- Unlike CSubst's value map, the variable map can only qualify a CVar to
-- another CVar; class-default qualification never substitutes expressions.
data ClassDefaultQualEnv = ClassDefaultQualEnv {
        cdqTypeCons :: M.Map Id Id,
        cdqCons     :: M.Map Id Id,
        cdqVars     :: M.Map Id Id
    }

removeVar :: ClassDefaultQualEnv -> Id -> ClassDefaultQualEnv
removeVar env i = env { cdqVars = M.delete i (cdqVars env) }

removeVars :: ClassDefaultQualEnv -> [Id] -> ClassDefaultQualEnv
removeVars env is = env { cdqVars = foldr M.delete (cdqVars env) is }

qualConId :: ClassDefaultQualEnv -> Id -> Id
qualConId env i = M.findWithDefault i i (cdqCons env)

qualMaybeConId :: ClassDefaultQualEnv -> Maybe Id -> Maybe Id
qualMaybeConId env = fmap (qualConId env)

qualTypeConId :: ClassDefaultQualEnv -> Id -> Id
qualTypeConId env i = M.findWithDefault i i (cdqTypeCons env)

qualMaybeTypeConId :: ClassDefaultQualEnv -> Maybe Id -> Maybe Id
qualMaybeTypeConId env = fmap (qualTypeConId env)

qualVarExpr :: ClassDefaultQualEnv -> Id -> CExpr
qualVarExpr env i = CVar (M.findWithDefault i i (cdqVars env))

getPatVars :: CPat -> [Id]
getPatVars = S.toList . getPV

getDeflVars :: CDefl -> [Id]
getDeflVars = getLDefs


qualifyClassDefaultClauses :: ClassDefaultQualEnv -> [CClause] -> [CClause]
qualifyClassDefaultClauses env clauses
    | M.null (cdqTypeCons env) && M.null (cdqCons env) && M.null (cdqVars env) = clauses
    | otherwise = map (qualClause env) clauses

qualClause :: ClassDefaultQualEnv -> CClause -> CClause
qualClause env (CClause pats quals body) =
    let env' = removeVars env (concatMap getPatVars pats)
        (env'', quals') = qualQuals env' quals
    in  CClause (map (qualPat env) pats) quals' (qualExpr env'' body)

qualRule :: ClassDefaultQualEnv -> CRule -> CRule
qualRule env (CRule pragmas label quals body) =
    let (env', quals') = qualQuals env quals
    in  CRule pragmas (fmap (qualExpr env) label) quals' (qualExpr env' body)
qualRule env (CRuleNest pragmas label quals rules) =
    let (env', quals') = qualQuals env quals
    in  CRuleNest pragmas (fmap (qualExpr env) label) quals'
            (map (qualRule env') rules)

qualQuals :: ClassDefaultQualEnv -> [CQual] -> (ClassDefaultQualEnv, [CQual])
qualQuals startEnv oldQuals =
    let qualQual (env, newQuals) (CQFilter e) =
            (env, CQFilter (qualExpr env e) : newQuals)
        qualQual (env, newQuals) (CQGen t p e) =
            let env' = removeVars env (getPatVars p)
                newQual = CQGen (qualType env t) (qualPat env p)
                                  (qualExpr env e)
            in  (env', newQual : newQuals)
        (newEnv, revNewQuals) = foldl qualQual (startEnv, []) oldQuals
    in  (newEnv, reverse revNewQuals)

qualExpr :: ClassDefaultQualEnv -> CExpr -> CExpr
qualExpr env (CLam ei@(Right i) e) =
    CLam ei (qualExpr (removeVar env i) e)
qualExpr env (CLam ei@(Left _) e) = CLam ei (qualExpr env e)
qualExpr env (CLamT ei@(Right i) t e) =
    CLamT ei (qualQType env t) (qualExpr (removeVar env i) e)
qualExpr env (CLamT ei@(Left _) t e) =
    CLamT ei (qualQType env t) (qualExpr env e)
qualExpr env (Cletseq defs body) =
    let (env', defs') = qualSeqDefls env defs
    in  Cletseq defs' (qualExpr env' body)
qualExpr env (Cletrec defs body) =
    let env' = removeVars env (concatMap getDeflVars defs)
    in  Cletrec (map (qualDefl env') defs) (qualExpr env' body)
qualExpr env (CSelect e i) = CSelect (qualExpr env e) i
qualExpr env (CCon i es) = CCon (qualConId env i) (map (qualExpr env) es)
qualExpr env (Ccase pos e arms) =
    Ccase pos (qualExpr env e) (map qualArm arms)
  where
    qualArm (CCaseArm p quals body) =
        let env' = removeVars env (getPatVars p)
            (env'', quals') = qualQuals env' quals
        in  CCaseArm (qualPat env p) quals' (qualExpr env'' body)
qualExpr env (CStruct mb i fields) =
    CStruct mb (qualConId env i) (mapSnd (qualExpr env) fields)
qualExpr env (CStructUpd e fields) =
    CStructUpd (qualExpr env e) (mapSnd (qualExpr env) fields)
qualExpr env (Cwrite pos lhs rhs) =
    Cwrite pos (qualExpr env lhs) (qualExpr env rhs)
qualExpr _ e@(CAny {}) = e
qualExpr env (CVar i) = qualVarExpr env i
qualExpr env (CApply f es) = CApply (qualExpr env f) (map (qualExpr env) es)
qualExpr env (CTaskApply f es) =
    CTaskApply (qualExpr env f) (map (qualExpr env) es)
qualExpr env (CTaskApplyT f t es) =
    CTaskApplyT (qualExpr env f) (qualType env t) (map (qualExpr env) es)
qualExpr _ e@(CLit {}) = e
qualExpr env (CBinOp lhs op rhs) =
    CBinOp (qualExpr env lhs) op (qualExpr env rhs)
qualExpr env (CHasType e t) = CHasType (qualExpr env e) (qualQType env t)
qualExpr env (Cif pos cond yes no) =
    Cif pos (qualExpr env cond) (qualExpr env yes) (qualExpr env no)
qualExpr env (CSub pos e idx) = CSub pos (qualExpr env e) (qualExpr env idx)
qualExpr env (CSub2 e hi lo) =
    CSub2 (qualExpr env e) (qualExpr env hi) (qualExpr env lo)
qualExpr env (CSubUpdate pos vec (hi, lo) rhs) =
    CSubUpdate pos (qualExpr env vec)
        (qualExpr env hi, qualExpr env lo) (qualExpr env rhs)
qualExpr env (Cmodule pos stmts) = Cmodule pos (qualMStmts env stmts)
qualExpr env (Cinterface pos con defs) =
    let env' = removeVars env (concatMap getDeflVars defs)
    in  Cinterface pos (qualMaybeConId env con) (map (qualDefl env') defs)
qualExpr env (CmoduleVerilog name user clocks resets args fields sched paths) =
    CmoduleVerilog (qualExpr env name) user clocks resets
        (mapSnd (qualExpr env) args) fields sched paths
qualExpr env (CForeignFuncC i t) = CForeignFuncC i (qualQType env t)
qualExpr env (Cdo recursive stmts) = Cdo recursive (qualStmts env stmts)
qualExpr env (Caction pos stmts) = Caction pos (qualStmts env stmts)
qualExpr env (Crules pragmas rules) = Crules pragmas (map (qualRule env) rules)
qualExpr env (COper ops) = COper (map (qualOp env) ops)
qualExpr env (CCon1 ti ci e) =
    CCon1 (qualTypeConId env ti) (qualConId env ci) (qualExpr env e)
qualExpr env (CSelectTT ti e fi) =
    CSelectTT (qualTypeConId env ti) (qualExpr env e) fi
qualExpr env (CCon0 ti ci) =
    CCon0 (qualMaybeTypeConId env ti) (qualConId env ci)
qualExpr env (CConT ti ci es) =
    CConT (qualTypeConId env ti) (qualConId env ci) (map (qualExpr env) es)
qualExpr env (CStructT t fields) =
    CStructT (qualType env t) (mapSnd (qualExpr env) fields)
qualExpr env (CSelectT ti fi) = CSelectT (qualTypeConId env ti) fi
qualExpr env (CLitT t lit) = CLitT (qualType env t) lit
qualExpr env (CAnyT pos kind t) = CAnyT pos kind (qualType env t)
qualExpr env (CmoduleVerilogT t name user clocks resets args fields sched paths) =
    CmoduleVerilogT (qualType env t) (qualExpr env name) user clocks resets
        (mapSnd (qualExpr env) args) fields sched paths
qualExpr env (CForeignFuncCT i t) = CForeignFuncCT i (qualType env t)
qualExpr env (CTApply e ts) = CTApply (qualExpr env e) (map (qualType env) ts)
qualExpr _ e@(Cattributes {}) = e

qualSeqDefls :: ClassDefaultQualEnv -> [CDefl] -> (ClassDefaultQualEnv, [CDefl])
qualSeqDefls startEnv oldDefs =
    let qualSeq (env, newDefs) def =
            let env' = removeVars env (getDeflVars def)
            in  (env', qualDefl env def : newDefs)
        (newEnv, revNewDefs) = foldl qualSeq (startEnv, []) oldDefs
    in  (newEnv, reverse revNewDefs)

qualDefl :: ClassDefaultQualEnv -> CDefl -> CDefl
qualDefl env (CLValueSign def quals) =
    let (env', quals') = qualQuals env quals
    in  CLValueSign (qualDef env' def) quals'
qualDefl env (CLValue i clauses quals) =
    let (env', quals') = qualQuals env quals
    in  CLValue i (map (qualClause env') clauses) quals'
qualDefl env (CLMatch pat e) =
    CLMatch (qualPat env pat) (qualExpr env e)

qualDef :: ClassDefaultQualEnv -> CDef -> CDef
qualDef env (CDef i t clauses) =
    CDef i (qualQType env t) (map (qualClause env) clauses)
qualDef env (CDefT i vars t clauses) =
    CDefT i vars (qualQType env t)
        (map (qualClause env) clauses)

qualQType :: ClassDefaultQualEnv -> CQType -> CQType
qualQType env (CQType preds t) =
    CQType (map (qualPred env) preds) (qualType env t)

qualPred :: ClassDefaultQualEnv -> CPred -> CPred
qualPred env (CPred (CTypeclass cls) ts) =
    CPred (CTypeclass (qualTypeConId env cls)) (map (qualType env) ts)

-- Return the original type node when no type-constructor name changes.  This
-- avoids rebuilding unrelated type trees and composes well with CType interning.
qualType :: ClassDefaultQualEnv -> CType -> CType
qualType env t = changedOr t (qualTypeChanged env t)

qualTypeChanged :: ClassDefaultQualEnv -> CType -> Changed CType
qualTypeChanged env
    | M.null (cdqTypeCons env) = const Unchanged
    | otherwise = go
  where
    go (TVar {}) = Unchanged
    go (TCon (TyCon i k sort)) =
        case M.lookup i (cdqTypeCons env) of
          Nothing -> Unchanged
          Just i' -> Changed (TCon (TyCon i' k sort))
    go (TCon (TyNum {})) = Unchanged
    go (TCon (TyStr {})) = Unchanged
    go (TAp f a) = changed2 TAp f a (go f) (go a)
    go (TGen {}) = Unchanged
    go (TDefMonad {}) = Unchanged

qualPat :: ClassDefaultQualEnv -> CPat -> CPat
qualPat env (CPCon i pats) = CPCon (qualConId env i) (map (qualPat env) pats)
qualPat env (CPstruct mb i fields) =
    CPstruct mb (qualConId env i) (mapSnd (qualPat env) fields)
qualPat _ p@(CPVar {}) = p
qualPat env (CPAs i p) = CPAs i (qualPat env p)
qualPat _ p@(CPAny {}) = p
qualPat _ p@(CPLit {}) = p
qualPat _ p@(CPMixedLit {}) = p
qualPat env (CPOper ops) = CPOper (map qualPatOp ops)
  where
    qualPatOp (CPRand p) = CPRand (qualPat env p)
    qualPatOp (CPRator n i) = CPRator n i
qualPat env (CPCon1 ti ci p) =
    CPCon1 (qualTypeConId env ti) (qualConId env ci) (qualPat env p)
qualPat env (CPConTs ti ci ts pats) =
    CPConTs (qualTypeConId env ti) (qualConId env ci)
        (map (qualType env) ts) (map (qualPat env) pats)

qualStmts :: ClassDefaultQualEnv -> [CStmt] -> [CStmt]
qualStmts startEnv oldStmts =
    let qualOne (env, newStmts) stmt =
            let (env', stmt') = qualStmt env stmt
            in  (env', stmt' : newStmts)
        revNewStmts = snd (foldl qualOne (startEnv, []) oldStmts)
    in  reverse revNewStmts

qualStmt :: ClassDefaultQualEnv -> CStmt -> (ClassDefaultQualEnv, CStmt)
qualStmt env (CSBindT pat name props t e) =
    let env' = removeVars env (getPatVars pat)
        stmt' = CSBindT (qualPat env pat) (fmap (qualExpr env) name) props
                    (qualQType env t) (qualExpr env e)
    in  (env', stmt')
qualStmt env (CSBind pat name props e) =
    let env' = removeVars env (getPatVars pat)
        stmt' = CSBind (qualPat env pat) (fmap (qualExpr env) name) props
                    (qualExpr env e)
    in  (env', stmt')
qualStmt env (CSletseq defs) =
    let (env', defs') = qualSeqDefls env defs
    in  (env', CSletseq defs')
qualStmt env (CSletrec defs) =
    let env' = removeVars env (concatMap getDeflVars defs)
        stmt' = CSletrec (map (qualDefl env') defs)
    in  (env', stmt')
qualStmt env (CSExpr name e) = (env, CSExpr name (qualExpr env e))

qualMStmts :: ClassDefaultQualEnv -> [CMStmt] -> [CMStmt]
qualMStmts startEnv oldStmts =
    let qualOne (env, newStmts) (CMStmt stmt) =
            let (env', stmt') = qualStmt env stmt
            in  (env', CMStmt stmt' : newStmts)
        qualOne (env, newStmts) (CMrules e) =
            (env, CMrules (qualExpr env e) : newStmts)
        qualOne (env, newStmts) (CMinterface e) =
            (env, CMinterface (qualExpr env e) : newStmts)
        qualOne (env, newStmts) (CMTupleInterface pos es) =
            (env, CMTupleInterface pos (map (qualExpr env) es) : newStmts)
        revNewStmts = snd (foldl qualOne (startEnv, []) oldStmts)
    in  reverse revNewStmts

qualOp :: ClassDefaultQualEnv -> COp -> COp
qualOp env (CRand e) = CRand (qualExpr env e)
qualOp _ (CRator n i) = CRator n i
