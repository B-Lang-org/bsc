module ParseOp(parseOps,parseOp) where
import Util(mapSndM, findSame)
import PFPrint
import Id
import CSyntax
import Fixity
import Error(internalError, ErrMsg(..), ErrorHandle)
import ErrorMonad(ErrorMonad(..), convErrorMonadToIO)
import PreIds(idAssign)

-- import Debug.Trace

-- XXX insert fixity in identifiers

type FixTable = [(Id, Fixity)]

parseOps :: ErrorHandle -> CPackage -> IO CPackage
parseOps errh (CPackage i exps imps impsigs fixs defs includes) =
    let ft = map getFixes fixs ++ concatMap getImpFixes impsigs in
    --trace (show ft) $
    do
       defs' <- convErrorMonadToIO errh (mapM (pDefn ft) defs)
       return (CPackage i exps imps impsigs fixs defs' includes)

getFixes :: CFixity -> (Id, Fixity)
getFixes (CInfix  p i) = (i, FInfix  (fromInteger p))
getFixes (CInfixl p i) = (i, FInfixl (fromInteger p))
getFixes (CInfixr p i) = (i, FInfixr (fromInteger p))

getImpFixes :: CImportedSignature -> FixTable
getImpFixes (CImpSign _ _ (CSignature _ _ fixs _)) = map getFixes fixs

pDefn :: FixTable -> CDefn -> ErrorMonad CDefn
pDefn ft (Cinstance t ds) = do
    ds' <- mapM (pDefl ft) ds
    return (Cinstance t ds')
pDefn ft (CValueSign d) = do
    d' <- pDef ft d
    return (CValueSign d')

pDefn ft def@(Cstruct _ sst idk _ fs _) =
  case sst of
       SStruct -> checkDupls def "member" "structure" (iKName idk) (map cf_name fs)
       SInterface{} -> checkDupls def "method" "interface" (iKName idk) (map cf_name fs)
       SDataCon i _ -> checkDupls def "member" "substructure of union" i (map cf_name fs)
       -- These don't exist until later:
       -- Created by MakeSymTab
       SClass -> internalError("ParseOp.pDefn: unexpected structure type: SClass\n" ++ ppReadable def)
       -- Created by Deriving
       SPolyWrap _ _ _ -> internalError("ParseOp.pDefn: unexpected structure type: SPolyWrap\n" ++ ppReadable def)

pDefn ft def@(Cclass incoh cps idk is fdps fs) = do
  let pField f@(CField { cf_default = fcs }) = do
        fcs' <- mapM (pCClause ft) fcs
        return (f { cf_default = fcs' })
  fs' <- mapM pField fs
  let def' = Cclass incoh cps idk is fdps fs'
  checkDupls def' "function" "typeclass" (iKName idk) (map cf_name fs)

pDefn ft def@(Cdata { cd_name = idk, cd_original_summands = ocs }) =
    checkDupls def "member" "union" (iKName idk) (concatMap cos_names ocs)

pDefn ft d = return d

checkDupls :: CDefn -> String -> String -> Id -> [Id] -> ErrorMonad CDefn
checkDupls def element container_type container_name ids =
  let sameIds = findSame ids in
      if (null sameIds) then return def
      -- XXX could return all duplicates, but I think tons of duplicates are rare
      else case head sameIds of
           (dupId:sndId:_) ->
               EMError [(getPosition sndId,
                         EDupMem (pfpString dupId) element
                                 container_type (pfpString container_name))]
           _ -> internalError "ParseOp.checkDupls"

pDefl :: FixTable -> CDefl -> ErrorMonad CDefl
pDefl ft (CLValueSign d qs) = do
    d' <- pDef ft d
    qs' <- mapM (pQual ft) qs
    return (CLValueSign d' qs')
pDefl ft (CLValue i cs qs) = do
    cs' <- mapM (pCClause ft) cs
    qs' <- mapM (pQual ft) qs
    return (CLValue i cs' qs')
pDefl ft (CLMatch p e) = do
    p' <- pPat ft p
    e' <- pExpr ft e
    return (CLMatch p' e')

pGuard :: FixTable -> Maybe CExpr -> ErrorMonad (Maybe CExpr)
pGuard ft Nothing = return Nothing
pGuard ft (Just e) = pExpr ft e >>= return . Just

pDef :: FixTable -> CDef -> ErrorMonad CDef
pDef ft (CDef i t cs) = do
    cs' <- mapM (pCClause ft) cs
    return (CDef i t cs')
pDef ft deft@(CDefT _ _ _ _) = internalError("ParseOp.pdef: typed definition: " ++ (ppReadable deft))

pCClause :: FixTable -> CClause -> ErrorMonad CClause
pCClause ft (CClause ps qs e) = do
    ps' <- mapM (pPat ft) ps
    qs' <- mapM (pQual ft) qs
    e' <- pExpr ft e
    return (CClause ps' qs' e')

pQual :: FixTable -> CQual -> ErrorMonad CQual
pQual ft (CQGen t p e) = do
    p' <- pPat ft p
    e' <- pExpr ft e
    return (CQGen t p' e')
pQual ft (CQFilter e) = do
    e' <- pExpr ft e
    return (CQFilter e')

pPat :: FixTable -> CPat -> ErrorMonad CPat
pPat ft (CPCon i ps) = do
    ps' <- mapM (pPat ft) ps
    return (CPCon i ps')
pPat ft (CPstruct mb i ips) = do
    ips' <- mapSndM (pPat ft) ips
    return (CPstruct mb i ips')
pPat ft p@(CPVar _) = return p
pPat ft (CPAs i p) = do
    p' <- pPat ft p
    return (CPAs i p')
pPat ft p@(CPAny {}) = return p
pPat ft p@(CPLit _) = return p
pPat ft p@(CPMixedLit {}) = return p

-- typed patterns should not appear
pPat ft p = internalError("ParseOp.pPat: typed pattern: " ++ ppReadable p)

pExpr :: FixTable -> CExpr -> ErrorMonad CExpr
pExpr ft (CLam i e) = do
    e' <- pExpr ft e
    return (CLam i e')
pExpr ft (Cletrec ds e) = do
    ds' <- mapM (pDefl ft) ds
    e' <- pExpr ft e
    return (Cletrec ds' e')
pExpr ft (Cletseq ds e) = do
    ds' <- mapM (pDefl ft) ds
    e' <- pExpr ft e
    return (Cletseq ds' e')
pExpr ft (CSelect e i) = do
    e' <- pExpr ft e
    return (CSelect e' i)
pExpr ft (CCon i es) = do
    es' <- mapM (pExpr ft) es
    return (CCon i es')
pExpr ft (Ccase pos e as) = do
    e' <- pExpr ft e
    let pCaseArm arm = do
            new_pattern <- pPat ft (cca_pattern arm)
            new_filters <- mapM (pQual ft) (cca_filters arm)
            new_consequent <- pExpr ft (cca_consequent arm)
            return (CCaseArm { cca_pattern = new_pattern,
                               cca_filters = new_filters,
                               cca_consequent = new_consequent })
    as' <- mapM pCaseArm as
    return (Ccase pos e' as')
pExpr ft (CStruct mb i ies) = do
    ies' <- mapSndM (pExpr ft) ies
    return (CStruct mb i ies')
pExpr ft (CStructUpd e ies) = do
    e' <- pExpr ft e
    ies' <- mapSndM (pExpr ft) ies
    return (CStructUpd e' ies')
pExpr ft (Cwrite pos e v) = do
    e' <- pExpr ft e
    v' <- pExpr ft v
    return (Cwrite pos e' v')
pExpr ft e@(CAny {}) = return e
pExpr ft e@(CVar _) = return e
pExpr ft (CApply e es) = do
    e' <- pExpr ft e
    es' <- mapM (pExpr ft) es
    return (CApply e' es')
pExpr ft (CTaskApply e es) = do
    e' <- pExpr ft e
    es' <- mapM (pExpr ft) es
    return (CTaskApply e' es')
pExpr ft e@(CLit _) = return e
-- XXX it is naughty but convenient to replace
-- := by Cwrite in ParseOp
-- (since it is common to the Classic and BSV flows)
pExpr ft e@(CBinOp lhs i rhs) | i `qualEq` idAssign =
  pExpr ft (Cwrite (getPosition i) lhs rhs)
pExpr ft (CBinOp e1 o e2) = do
    e1' <- pExpr ft e1
    e2' <- pExpr ft e2
    return (CBinOp e1' o e2')
pExpr ft (CHasType e t) = do
    e' <- pExpr ft e
    return (CHasType e' t)
pExpr ft (Cif pos e1 e2 e3) = do
    e1' <- pExpr ft e1
    e2' <- pExpr ft e2
    e3' <- pExpr ft e3
    return (Cif pos e1' e2' e3')
pExpr ft (CSub pos e1 e2) = do
    e1' <- pExpr ft e1
    e2' <- pExpr ft e2
    return (CSub pos e1' e2')
pExpr ft (CSub2 e1 e2 e3) = do
    e1' <- pExpr ft e1
    e2' <- pExpr ft e2
    e3' <- pExpr ft e3
    return (CSub2 e1' e2' e3')
pExpr ft (CSubUpdate pos e_vec (e_h, e_l) e_rhs) = do
    e_vec' <- pExpr ft e_vec
    e_h'   <- pExpr ft e_h
    e_l'   <- pExpr ft e_l
    e_rhs' <- pExpr ft e_rhs
    return (CSubUpdate pos e_vec' (e_h', e_l') e_rhs')
pExpr ft (Cmodule pos is) = do
    is' <- mapM (pMStmt ft) is
    return (Cmodule pos is')
pExpr ft (Cinterface pos i ds) = do
    ds' <- mapM (pDefl ft) ds
    return (Cinterface pos i ds')
pExpr ft (CmoduleVerilog n ui ck rs ses ms vi ps) = do
    n' <- pExpr ft n
    ses' <- mapSndM (pExpr ft) ses
    return (CmoduleVerilog n' ui ck rs ses' ms vi ps)
pExpr ft e@(CForeignFuncC { }) = return e
pExpr ft (Cdo r ss) = do
    ss' <- mapM (pStmt ft) ss
    return (Cdo r ss')
pExpr ft (Caction pos ss) = do
    ss' <- mapM (pStmt ft) ss
    return (Caction pos ss')
pExpr ft (Crules ps rs) = do
    rs' <- mapM (pRule ft) rs
    return (Crules ps rs')
pExpr ft (COper os) = do
    os' <- mapM (pOp ft) os
    parseOp ft os'
pExpr ft e@(Cattributes _) = return e  -- XXX is this expected?
pExpr ft e = internalError ("ParseOp.pExpr: unexpected expression: " ++ ppReadable e)

pStmt :: FixTable -> CStmt -> ErrorMonad CStmt
pStmt ft (CSBindT p name pprops t e) = do
    p' <- pPat ft p
    e' <- pExpr ft e
    return (CSBindT p' name pprops t e')
pStmt ft (CSBind p name pprops e) = do
    p' <- pPat ft p
    e' <- pExpr ft e
    return (CSBind p' name pprops e')
pStmt ft (CSletrec ds) = do
    ds' <- mapM (pDefl ft) ds
    return (CSletrec ds')
pStmt ft (CSletseq ds) = do
    ds' <- mapM (pDefl ft) ds
    return (CSletseq ds')
pStmt ft (CSExpr name e) = do
    e' <- pExpr ft e
    return (CSExpr name e')

pMStmt :: FixTable -> CMStmt -> ErrorMonad CMStmt
pMStmt ft (CMStmt s) = do
    s' <- pStmt ft s
    return (CMStmt s')
pMStmt ft (CMrules e) = do
    e' <- pExpr ft e
    return (CMrules e')
pMStmt ft (CMinterface e) = do
    e' <- pExpr ft e
    return (CMinterface e')
pMStmt ft (CMTupleInterface pos es) = do
    es' <- mapM (pExpr ft) es
    return (CMTupleInterface pos es')

pRule :: FixTable -> CRule -> ErrorMonad CRule
pRule ft (CRule ps g qs e) = do
    g' <- pGuard ft g
    qs' <- mapM (pQual ft) qs
    e' <- pExpr ft e
    return (CRule ps g' qs' e')
pRule ft (CRuleNest ps g qs rs) = do
    g' <- pGuard ft g
    qs' <- mapM (pQual ft) qs
    rs' <- mapM (pRule ft) rs
    return (CRuleNest ps g' qs' rs')

pOp :: FixTable -> COp -> ErrorMonad COp
pOp ft (CRand e) = pExpr ft e >>= return . CRand
pOp ft e = return e

parseOp :: FixTable -> [COp] -> ErrorMonad CExpr
parseOp ft ops = doOne ft ops [] []

doOne :: FixTable -> [COp] -> [(Int, Id)] -> [CExpr] -> ErrorMonad CExpr
doOne ft [] [] [e] = return e
doOne ft [] [] es = internalError ("ParseOp.doOne: Bad operand stack "++ppDebug es)
doOne ft [] ((a,o):os) es = doOp ft a o [] os es
doOne ft (CRand e:rs) os es = doOne ft rs os (e:es)
doOne ft (CRator a iop:rs) [] es = doOne ft rs [(a,iop)] es
doOne ft rrs@(CRator ia iop:rs) oos@((sa,sop):os) es =
        let (iprec,iass) = precOfA ft ia iop
            (sprec,sass) = precOfA ft sa sop
        in  {-if iass==FPrefix iprec && iprec <= sprec then
                EMError (getIdPosition iop, ESyntax (ppId iop) [])
            else-}
            if iprec==sprec && (iass/=sass || iass==FInfix iprec) {- && sass /= FPrefix sprec-} then
                EMError [(getIdPosition sop, EAmbOper (pfpString sop) (pfpString iop))]
            else if iprec>sprec || iprec==sprec && iass==FInfixr iprec then
                doOne ft rs ((ia,iop):oos) es
            else
                doOp ft sa sop rrs os es
doOp :: FixTable -> Int -> Id -> [COp] -> [(Int, Id)] -> [CExpr] -> ErrorMonad CExpr
doOp ft a op rs os es =
{-
    if idFString op == fsMinus && a == 1 then
        case es of
            e:es' -> doOne ft rs os (ENegate e : es')
            _ -> internalError ("Bad operator arity (1) for "++pfpString op)
    else
-}
        case es of
            e1:e2:es' -> -- XXX := to Cwrite (see above)
                         do let e' = if (op `qualEq` idAssign) then
                                       Cwrite (getPosition op) e2 e1
                                     else CBinOp e2 op e1
                            doOne ft rs os (e' : es')
            _ -> internalError ("ParseOp.doOp: Bad operator arity (2) for "++pfpString op)

precOfA :: FixTable -> Int -> Id -> (Int, Fixity)
precOfA ft _ i =
    case getIdFixity ft i of
    f@(FInfix  i) -> (i, f)
    f@(FInfixl i) -> (i, f)
    f@(FInfixr i) -> (i, f)
    i -> internalError ("ParseOp.precOfA: bad op: " ++ show i)

getIdFixity :: FixTable -> Id -> Fixity
getIdFixity ft i =
    case lookup i ft of
    Nothing -> defaultFixity
    Just f -> f
