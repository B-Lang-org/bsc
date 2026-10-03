module CQualifyClassDefaults (
        qualifyClassDefaults
    ) where

import Data.List(mapAccumL)
import qualified Data.Map as M
import qualified Data.Set as S

import Assump(Assump(..))
import Changed(Changed(..), changed2, changedOr)
import CFreeVars(getFVC, getFTCC, getLDefs, getPV)
import CSyntax
import Error(internalError, ErrorHandle, ErrMsg(..), bsErrorUnsafe)
import Id(Id, getIdString)
import PFPrint
import SymTab
import Util(mapSnd, quote)


-- The three namespaces which can contain free names in a class default.
-- Unlike CSubst's value map, the variable map can only qualify a CVar to
-- another CVar; class-default qualification never substitutes expressions.
-- Lexical bindings mask entries in the fixed free-variable map.
data ClassDefaultQualScope = ClassDefaultQualScope {
        cdqTypeCons :: M.Map Id Id,
        cdqCons     :: M.Map Id Id,
        cdqVars     :: M.Map Id Id,
        cdqBound    :: S.Set Id
    }

bindVars :: [Id] -> ClassDefaultQualScope -> ClassDefaultQualScope
bindVars is scope = scope { cdqBound = S.union (S.fromList is) (cdqBound scope) }

qualConId :: ClassDefaultQualScope -> Id -> Id
qualConId scope i = M.findWithDefault i i (cdqCons scope)

qualMaybeConId :: ClassDefaultQualScope -> Maybe Id -> Maybe Id
qualMaybeConId scope = fmap (qualConId scope)

qualTypeConId :: ClassDefaultQualScope -> Id -> Id
qualTypeConId scope i = M.findWithDefault i i (cdqTypeCons scope)

qualMaybeTypeConId :: ClassDefaultQualScope -> Maybe Id -> Maybe Id
qualMaybeTypeConId scope = fmap (qualTypeConId scope)

qualVarExpr :: ClassDefaultQualScope -> Id -> CExpr
qualVarExpr scope i
    | i `S.member` cdqBound scope = CVar i
    | otherwise = CVar (M.findWithDefault i i (cdqVars scope))

getPatVars :: CPat -> [Id]
getPatVars = S.toList . getPV

getDeflVars :: CDefl -> [Id]
getDeflVars = getLDefs


qualifyClassDefaults :: ErrorHandle -> SymTab -> CPackage -> CPackage
qualifyClassDefaults errh symt
        (CPackage name exports imports impsigs fixities defns includes) =
    CPackage name exports imports impsigs fixities (map qualifyDefn defns) includes
  where
    qualifyDefn (Cclass incoh preds idk vars deps ats fields) =
        Cclass incoh preds idk vars deps ats (map qualifyField fields)
    qualifyDefn defn = defn

    qualifyField field@(CField { cf_default = [] }) = field
    qualifyField field@(CField { cf_default = clauses }) =
        field { cf_default = qualifyClassDefaultClauses scope clauses }
      where
        (freeCons, freeVars) = unzip (map getFVC clauses)
        conMap = M.fromList (map qualifyCon (S.toList (S.unions freeCons)))
        varMap = M.fromList (map qualifyVar (S.toList (S.unions freeVars)))
        typeMap = M.fromList
            (map qualifyTypeCon (S.toList (S.unions (map getFTCC clauses))))
        scope = ClassDefaultQualScope typeMap conMap varMap S.empty

    qualifyCon con =
        case findCon symt con of
          Just [ConInfo { ci_assump = (qualified :>: _) }] -> (con, qualified)
          Just _ ->
              let msg = "The signature file generation for typeclass " ++
                        "defaults cannot disambiguate the constructor " ++
                        quote (getIdString con) ++ ".  Perhaps adding " ++
                        "a package qualifier will help."
              in  bsErrorUnsafe errh [(getPosition con, EGeneric msg)]
          Nothing ->
              -- It could be a struct/interface (or an alias of one?).
              case findType symt con of
                Just (TypeInfo (Just qualified) _ _ _ _) -> (con, qualified)
                _ -> internalError ("qualifyClassDefaults: " ++
                                    "constructor not found: " ++
                                    ppReadable con)

    qualifyTypeCon tycon =
        case findType symt tycon of
          Just (TypeInfo (Just qualified) _ _ _ _) -> (tycon, qualified)
          Just (TypeInfo Nothing _ _ _ _) ->
              internalError ("qualifyClassDefaults: " ++
                             "unexpected numeric or string type: " ++
                             ppReadable tycon)
          Nothing -> internalError ("qualifyClassDefaults: " ++
                                    "type not found: " ++ ppReadable tycon)

    qualifyVar var =
        case findVar symt var of
          Just (VarInfo _ (qualified :>: _) _ _) -> (var, qualified)
          Nothing -> internalError ("qualifyClassDefaults: " ++
                                    "var not found: " ++ ppReadable var)

qualifyClassDefaultClauses :: ClassDefaultQualScope -> [CClause] -> [CClause]
qualifyClassDefaultClauses scope clauses
    | M.null (cdqTypeCons scope) &&
      M.null (cdqCons scope) &&
      M.null (cdqVars scope) = clauses
    | otherwise = map (qualClause scope) clauses

qualClause :: ClassDefaultQualScope -> CClause -> CClause
qualClause scope (CClause pats quals body) =
    let patScope = bindVars (concatMap getPatVars pats) scope
        (bodyScope, quals') = qualQuals patScope quals
    in  CClause (map (qualPat scope) pats) quals'
            (qualExpr bodyScope body)

qualRule :: ClassDefaultQualScope -> CRule -> CRule
qualRule scope (CRule pragmas label quals body) =
    let (bodyScope, quals') = qualQuals scope quals
    in  CRule pragmas (fmap (qualExpr scope) label) quals'
            (qualExpr bodyScope body)
qualRule scope (CRuleNest pragmas label quals rules) =
    let (bodyScope, quals') = qualQuals scope quals
    in  CRuleNest pragmas (fmap (qualExpr scope) label) quals'
            (map (qualRule bodyScope) rules)

qualQuals :: ClassDefaultQualScope
          -> [CQual]
          -> (ClassDefaultQualScope, [CQual])
qualQuals = mapAccumL qualQual
  where
    qualQual scope (CQFilter e) =
        (scope, CQFilter (qualExpr scope e))
    qualQual scope (CQGen t p e) =
        (bindVars (getPatVars p) scope,
         CQGen (qualType scope t) (qualPat scope p) (qualExpr scope e))

qualExpr :: ClassDefaultQualScope -> CExpr -> CExpr
qualExpr scope (CLam ei@(Right i) e) =
    CLam ei (qualExpr (bindVars [i] scope) e)
qualExpr scope (CLam ei@(Left _) e) = CLam ei (qualExpr scope e)
qualExpr scope (CLamT ei@(Right i) t e) =
    CLamT ei (qualQType scope t) (qualExpr (bindVars [i] scope) e)
qualExpr scope (CLamT ei@(Left _) t e) =
    CLamT ei (qualQType scope t) (qualExpr scope e)
qualExpr scope (Cletseq defs body) =
    let (bodyScope, defs') = qualSeqDefls scope defs
    in  Cletseq defs' (qualExpr bodyScope body)
qualExpr scope (Cletrec defs body) =
    let bodyScope = bindVars (concatMap getDeflVars defs) scope
    in  Cletrec (map (qualDefl bodyScope) defs)
            (qualExpr bodyScope body)
qualExpr env (CSelect e i) = CSelect (qualExpr env e) i
qualExpr env (CCon i es) = CCon (qualConId env i) (map (qualExpr env) es)
qualExpr env (Ccase pos e arms) =
    Ccase pos (qualExpr env e) (map qualArm arms)
  where
    qualArm (CCaseArm p quals body) =
        let patScope = bindVars (getPatVars p) env
            (bodyScope, quals') = qualQuals patScope quals
        in  CCaseArm (qualPat env p) quals' (qualExpr bodyScope body)
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
    let bodyScope = bindVars (concatMap getDeflVars defs) env
    in  Cinterface pos (qualMaybeConId env con)
            (map (qualDefl bodyScope) defs)
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

qualSeqDefls :: ClassDefaultQualScope
              -> [CDefl]
              -> (ClassDefaultQualScope, [CDefl])
qualSeqDefls = mapAccumL qualSeq
  where
    qualSeq scope def =
        (bindVars (getDeflVars def) scope, qualDefl scope def)

qualDefl :: ClassDefaultQualScope -> CDefl -> CDefl
qualDefl env (CLValueSign def quals) =
    let (env', quals') = qualQuals env quals
    in  CLValueSign (qualDef env' def) quals'
qualDefl env (CLValue i clauses quals) =
    let (env', quals') = qualQuals env quals
    in  CLValue i (map (qualClause env') clauses) quals'
qualDefl env (CLMatch pat e) =
    CLMatch (qualPat env pat) (qualExpr env e)

qualDef :: ClassDefaultQualScope -> CDef -> CDef
qualDef env (CDef i t clauses) =
    CDef i (qualQType env t) (map (qualClause env) clauses)
qualDef env (CDefT i vars t clauses) =
    CDefT i vars (qualQType env t)
        (map (qualClause env) clauses)

qualQType :: ClassDefaultQualScope -> CQType -> CQType
qualQType env (CQType preds t) =
    CQType (map (qualPred env) preds) (qualType env t)

qualPred :: ClassDefaultQualScope -> CPred -> CPred
qualPred env (CPred (CTypeclass cls) ts) =
    CPred (CTypeclass (qualTypeConId env cls)) (map (qualType env) ts)

-- Return the original type node when no type-constructor name changes.  This
-- avoids rebuilding unrelated type trees and composes well with CType interning.
qualType :: ClassDefaultQualScope -> CType -> CType
qualType env t = changedOr t (qualTypeChanged env t)

qualTypeChanged :: ClassDefaultQualScope -> CType -> Changed CType
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

qualPat :: ClassDefaultQualScope -> CPat -> CPat
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

qualStmts :: ClassDefaultQualScope -> [CStmt] -> [CStmt]
qualStmts startScope = snd . mapAccumL qualStmt startScope

qualStmt :: ClassDefaultQualScope
         -> CStmt
         -> (ClassDefaultQualScope, CStmt)
qualStmt env (CSBindT pat name props t e) =
    let env' = bindVars (getPatVars pat) env
        stmt' = CSBindT (qualPat env pat) (fmap (qualExpr env) name) props
                    (qualQType env t) (qualExpr env e)
    in  (env', stmt')
qualStmt env (CSBind pat name props e) =
    let env' = bindVars (getPatVars pat) env
        stmt' = CSBind (qualPat env pat) (fmap (qualExpr env) name) props
                    (qualExpr env e)
    in  (env', stmt')
qualStmt env (CSletseq defs) =
    let (env', defs') = qualSeqDefls env defs
    in  (env', CSletseq defs')
qualStmt env (CSletrec defs) =
    let env' = bindVars (concatMap getDeflVars defs) env
        stmt' = CSletrec (map (qualDefl env') defs)
    in  (env', stmt')
qualStmt env (CSExpr name e) = (env, CSExpr name (qualExpr env e))

qualMStmts :: ClassDefaultQualScope -> [CMStmt] -> [CMStmt]
qualMStmts startScope = snd . mapAccumL qualMStmt startScope
  where
    qualMStmt scope (CMStmt stmt) =
        let (scope', stmt') = qualStmt scope stmt
        in  (scope', CMStmt stmt')
    qualMStmt scope (CMrules e) =
        (scope, CMrules (qualExpr scope e))
    qualMStmt scope (CMinterface e) =
        (scope, CMinterface (qualExpr scope e))
    qualMStmt scope (CMTupleInterface pos es) =
        (scope, CMTupleInterface pos (map (qualExpr scope) es))

qualOp :: ClassDefaultQualScope -> COp -> COp
qualOp env (CRand e) = CRand (qualExpr env e)
qualOp _ (CRator n i) = CRator n i
