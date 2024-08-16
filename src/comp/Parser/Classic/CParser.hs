{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ > 800)
{-# OPTIONS_GHC -O0 #-}
#endif
module Parser.Classic.CParser(pPackage, pDefnsAndEOF, errSyntax) where

import Data.List(nub)

import Parse
import IntLit
import FStringCompat
import PreStrings(fsBar, fsStar, fsHash, fsDollar, fsLT, fsLTGT, fsLsh, fsNoinline,
                  fsASSERT, fsFire, fsEnabled, fsNo, fsImplicit, fsConditions,
                  fsCan, fsSchedule, fsFirst, fsClockCrossing, fsRule,
                  fsEmpty, fsConfOp, fsHide, fsHideAll,
                  fsAggressiveImplicitConditions, fsConservativeImplicitConditions,
                  fsNoWarn, fsWarnAllConflicts)
import Position
import Error(internalError, EMsg, ErrMsg(..))
import CSyntax
import CSyntaxUtil
import CType(cTNum, cTStr)
import VModInfo(VPathInfo(..), VSchedInfo, VPort,
                VFieldInfo(..), VeriPortProp(..), VName(..),
                VMethodConflictInfo)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..), MethodConflictOp(..))
import Id
import PreIds
import Lex
import BinParse
import Pragma

-- import Debug.Trace

-- XXX
import IOUtil(progArgs)

infix 6 >>>> , >>>>> , >>>>>> , >>>>>>> , {- >>>>>>>> , -} >>>>>>>>>

-- XXX
useLayout :: Bool
useLayout = notElem "-no-use-layout" progArgs

type CParser a = Parser [Token] a

pPackage :: CParser CPackage
pPackage =
    (l L_package ..+
    pModId +.+ pExports +.+ l L_where ..+
    block noTrig
        (sepBy pImport dsm +.+ osm ..+
            sepBy pFixity dsm +.+ osm ..+
            pDefns) +..
                osm >>>>>> (\ a b c d e -> CPackage a b c d e [])) +..
                    eof

pExports :: CParser (Either [CExport] [CExport])
pExports  =  (lp ..+ sepBy pExpId cm +.. rp >>- Left)
         ||! (literal (mkFString "hiding") ..+ lp ..+ sepBy pExpExcludedId cm +.. rp >>- Right)
         ||! succeed (Right [])

pExpId :: CParser CExport
pExpId = (l L_package ..+ pModId >>- CExpPkg)
     ||! (pConId `into` \ i ->
          lp ..+ dotdot +.. rp .> CExpConAll i
          ||! succeed (CExpCon i))
     ||! pVarId >>- CExpVar

-- cannot exclude packages or constructor fields
pExpExcludedId :: CParser CExport
pExpExcludedId = pConId >>- CExpCon
             ||! pVarId >>- CExpVar

pImport :: CParser CImport
pImport = l L_import ..+ pOptQualified +.+ pModId >>> CImpId

pFixity :: CParser CFixity
pFixity =
            l L_infix  ..+ int +.+ pOper >>> CInfix
        ||! l L_infixl ..+ int +.+ pOper >>> CInfixl
        ||! l L_infixr ..+ int +.+ pOper >>> CInfixr

pOptQualified :: CParser Bool
pOptQualified = l L_qualified .> True ||! succeed False

pExpr :: CParser CExpr
pExpr = exp0

exp0 :: CParser CExpr
exp0 = exp00                          >>- (\x->case x of [CRand e] -> e; _ -> COper x)

exp00 :: CParser [COp]
exp00 =   {-negat +.+ expX +.+ exp01  >>- (\ (u,(e,es)) -> CRator 1 u : CRand e : es)
        ||! -} expX +.+ exp01                >>- (\ (e, es) -> CRand e : es)
exp01 :: CParser [COp]
exp01 =   pOper +.+ exp00             >>- (\ (o, es) -> CRator 2 o : es)
        ||! succeed                             []

expX :: CParser CExpr
expX =      blockKwOf L_let pDeflM +.+ l L_in ..+ exp0                >>> Cletrec
        ||! blockKwOf L_letseq pDeflM +.+ l L_in ..+ exp0             >>> Cletseq
        ||! l L_case +.+ exp0 +.+ l L_of ..+ blockOf noTrig pCaseArm  >>>> Ccase
        ||! getPos +.+ l L_lam ..+ many1 pPat +.+ l L_rarrow ..+ exp0 >>>> cLam
        ||! l L_if +.+ exp0 +.+ osm ..+
            l L_then ..+ exp0 +.+ osm ..+
            l L_else ..+ exp0                                         >>>>> Cif
        ||! pTyConId +.+ pFieldBlock                                  >>> CStruct Nothing
        ||! l L_valueOf +.+ atyp                                      >>- ( \ (p, t) -> cVApply (setIdPosition p idValueOf) [CHasType (anyExprAt p) (CQType [] (TAp (cTCon idBit) t))])
        ||! l L_stringOf +.+ atyp                                     >>- ( \ (p, t) -> cVApply (setIdPosition p idStringOf) [CHasType (anyExprAt p) (CQType [] (TAp (cTCon idStringProxy) t))])
        ||! aexp `into` (\ e ->
                blockKwOf L_where pDefl                               >>- flip Cletrec e
            ||! l L_lbra ..+ exp0 `into` (\ e' ->
                                    l L_colon ..+ exp0 +.. l L_rbra   >>- CSub2 e e')
            ||! dc ..+ pQType                                         >>- CHasType e
            ||! pFieldBlock                                           >>- CStructUpd e
            ||! many aexp                                             >>- cmtApply 9 e)
--        ||! blkexp
        -- The following could be atomic
        ||! blockKw L_rules pRules                                    >>- (Crules [])
        ||! (getPos `into` \ pos -> l L_interface `into` \ tp -> (pTyConId >>- Just) +.+ blockOf tp pTDefl >>> Cinterface pos)
        ||! pModule

-- blocks that can be regarded as atomic
blkexp :: CParser CExpr
blkexp =    l L_do ..+ blockOf noTrig pStmt                           >>- Cdo True
        ||! l L_action `into` \pos -> blockOf noTrig pStmt            >>- Caction pos

pModule :: CParser CExpr
pModule = l L_module `into` \ pos ->
             blockOf noTrig pMStmt                                    >>- Cmodule pos
        ||! l L_verilog ..+ aexp +.+ pOParen (sepBy1 (pParen (pString +.+ cm ..+ pExpr)) cm) +.+
                sepBy1 pString cm +.+ sepBy pString cm +.+
                pOParen (sepBy1 (pParen (pString +.+ pVeriPortProps +.+ cm ..+ pExpr)) cm) +.+
                blockOf noTrig pField +.+ pSchedInfo +.+ pPathInfo   >>>>>>>>> xClassicModuleVerilog
  where pPathInfo :: CParser VPathInfo
        pPathInfo = succeed (VPathInfo [])
        pField :: CParser VFieldInfo
        pField = pFieldId +.+ pOMult +.+ eq ..+ many pVeriPort
                 +.+ pOPort "output" +.+ pOPort "enable"             >>>>>> mkMethod
        pOPort :: String -> CParser (Maybe VPort)
        pOPort s = option (cm ..+ literal (mkFString s) ..+ pVeriPort)
        pVeriPort :: CParser VPort
        pVeriPort = (pString >>- VName) +.+ pVeriPortProps
        pVeriPortProps :: CParser [VeriPortProp]
        pVeriPortProps = optProps pVeriProp
        pVeriProp :: CParser VeriPortProp
        pVeriProp = literal (mkFString "reg") .> VPreg
                ||! literal (mkFString "const") .> VPconst
                ||! literal (mkFString "unused") .> VPunused
                ||! literal (mkFString "inhigh") .> VPinhigh
        mkMethod i n vps mo me = Method i Nothing Nothing n vps Nothing Nothing

pMStmt :: CParser CMStmt
pMStmt =   pModuleInterface
       ||! pModuleRules
       ||! pStmt            >>- CMStmt

pModuleInterface :: CParser CMStmt
pModuleInterface = getPos `into` \pos -> l L_interface `into` \ tp ->
            lp ..+ sepBy exp0 (l L_comma) +.. rp    >>- CMTupleInterface tp
        ||! opt pTyConId +.+ blockOf tp pTDefl      >>- (\ (oty, defs) -> CMinterface (Cinterface pos oty defs))

pModuleRules :: CParser CMStmt
pModuleRules = blockKw L_rules pRules >>- CMrules . (Crules [])

-- XXX the user does not specify the ruleBetweenMethods info, etc.
pSchedInfo :: CParser VSchedInfo
pSchedInfo = pMethodConflictInfo >>- (\mci -> SchedInfo mci [] [] [])

pMethodConflictInfo :: CParser VMethodConflictInfo
pMethodConflictInfo =
    l L_lbra ..+ sepBy (pMeths +.+ pMethodConflictOp +.+ pMeths) cm +.. l L_rbra        >>- vMethodConflictInfo
         ||! succeed (MethodConflictInfo [] [] [] [] [] [] [])
  where pMethodConflictOp = ltgt .> CF ||! lt .> SB ||! ltlt .> SBR ||! confOp .> C
        pMeths = l L_lbra ..+ sepBy pFieldId cm +.. l L_rbra ||! pFieldId >>- (:[])
        vMethodConflictInfo xs =
            MethodConflictInfo [(i1, i2) | (is1, (CF, is2)) <- xs, i1 <- is1, i2 <- is2]
                                  [(i1, i2) | (is1, (SB, is2)) <- xs, i1 <- is1, i2 <- is2]
                                  [] -- ME (not supported)
                                  [] -- P (not supported)
                                  [(i1, i2) | (is1, (SBR, is2)) <- xs, i1 <- is1, i2 <- is2]
                                  [(i1, i2) | (is1, (C, is2))   <- xs, i1 <- is1, i2 <- is2]
                                  [] -- EXT (not supported)

pOMult :: CParser Integer
pOMult = l L_lbra ..+ int +.. l L_rbra ||! succeed 1

pOParen :: CParser [a] -> CParser [a]
pOParen p = lp ..+ p +.. rp
        ||! succeed []

pParen :: CParser a -> CParser a
pParen p = lp ..+ p +.. rp

pStmt :: CParser CStmt
pStmt = (pHVarId `into` \ i ->
        dc ..+ (pQType `into` \ t ->
                sm ..+ (piHEq i `into` \ j ->
                            l L_larrow ..+ pExpr  >>- CSBindT (kCPVar j) Nothing [] t)
            ||! l L_larrow ..+ pExpr              >>- CSBindT (kCPVar i) Nothing [] t)
            ||!  l L_larrow ..+ pExpr             >>- CSBind  (kCPVar i) Nothing [])
--        ||! pPat +.+ dc ..+ pQType +.+ l L_larrow ..+ pExpr    >>>> CSBindT
        ||! (pPat `into` \ p ->
                        dc ..+ pQType +.+ l L_larrow ..+ pExpr   >>> CSBindT p Nothing []
                    ||! l L_larrow ..+ pExpr      >>- CSBind p Nothing [])
        ||! blockKwOf L_let pDeflM                >>- CSletrec
        ||! blockKwOf L_letseq pDeflM             >>- CSletseq
        ||! pExpr                                 >>- CSExpr Nothing

kCPVar :: Id -> CPat
kCPVar i = (CPVar (setKeepId i))

aexp :: CParser CExpr
aexp = aexp' +.+ many suff              >>> foldl (\ x f -> f x)

suff :: CParser (CExpr -> CExpr)
suff =  dot ..+ pFieldId                >>- flip CSelect
    ||! l L_lbra ..+ exp0 `into` (\ e' ->
        l L_colon ..+ exp0 +.. l L_rbra >>- \ e2 -> \ e -> CSub2 e e' e2)

aexp' :: CParser CExpr
aexp' =     pAny                           >>- anyExprAt
        ||! pVarId                         >>- cVar
        ||! pConId                         >>- (\ i -> CCon i [])
        ||! lp ..+ dot ..+ pFieldId +.. rp >>- CLam (Right id_x) . CSelect (cVar id_x)
        ||! lp +.+ sepBy exp0 (l L_comma) +.. rp  >>> mkTuple
        ||! numericLit
        ||! string
        ||! char
        ||! blkexp -- XXX maybe it should be expX

pQType :: CParser CQType
pQType = pPreds +.+ pType                          >>> CQType

pPreds :: CParser [CPred]
pPreds = lp ..+ sepBy1 pPred cm +.. rp +.. l L_irarrow
     ||| succeed []

pPred :: CParser CPred
pPred = pTypeclass +.+ many atyp                   >>> CPred

pTypeclass :: CParser CTypeclass
pTypeclass = pTyConId                              >>- CTypeclass

pType :: CParser CType
pType = typ0

atyp :: CParser CType
atyp =      pTyConId                               >>- cTCon
        ||! pTyVarId                               >>- cTVar
        ||! pTyNumId
        ||! pTyStrId
        ||! lp +.+ sepBy typ0 (l L_comma) +.. rp   >>> tMkTuple

typ0 :: CParser CType
typ0 = typ10 `into` \ t ->
            l L_rarrow +.+ typ0                    >>> (\ p r -> cTApplys (cTCon (idArrow p)) [t,r])
        ||! succeed                                t

--mkTBinOp l op r = cTApplys (cTCon op) [l, r]

typ10 :: CParser CType
typ10 = atyp +.+ many atyp                         >>> cTApplys

pDeflM :: CParser CDefl
pDeflM = pDefl
     ||! pPat +.+ eq ..+ pExpr                     >>> CLMatch

pDefl :: CParser CDefl
pDefl =  (pVarId +.+ dc ..+ pQType `into` \ (i,t) ->
                dsm ..+ pClauses1 i               >>- (\ e -> CLValueSign (CDef i t e) [])
            ||! eq ..+ exp0                       >>- (\ e -> CLValueSign (CDef i t [CClause [] [] e]) []))
    ||! pClauseAny `into` \ (i, c) -> pClauses i  >>- (\ cs -> CLValue i (c:cs) [])

pTDefl :: CParser CDefl
pTDefl = pDefl `into` \ d ->
                l L_when ..+ sepBy1 pQual cm      >>- updWhen d
            ||! succeed                           d
  where updWhen (CLValueSign d _) qs = CLValueSign d qs
        updWhen (CLValue i cs  _) qs = CLValue i cs  qs
        updWhen (CLMatch _ _) _ = internalError "CParser.pTDefl.updWhen: CLMatch"

cLam :: Position -> [CPat] -> CExpr -> CExpr
-- We special-case CPVar and CPAny because the typechecker can
-- propagate more type information in those cases.
cLam _ [] e = e -- many1 means this case should be impossible.
cLam pos (CPVar i   : ps)  e = CLam (Right i)   $ cLam pos ps e
cLam pos (CPAny pos' : ps) e = CLam (Left pos') $ cLam pos ps e
cLam pos ps e = Cletseq [CLValue id_lam' [CClause ps [] e] []] (CVar id_lam')
  where id_lam' = id_lam pos

pFieldDef :: CParser (Id, CExpr)
pFieldDef = pFieldId +.+ eq ..+ pExpr

pFieldBlock :: CParser [(Id, CExpr)]
pFieldBlock = blockBrOf pFieldDef                -- use `;'
--pFieldBlock = hBlock (sepBy pFieldDef cm)        -- use `,'

blockOf :: Position -> CParser a -> CParser [a]
blockOf tp p = startBlock tp ..+ hBlock (sepBy p dsm +.. osm)

blockKwOf :: LexItem -> CParser a -> CParser [a]
blockKwOf kw p = l kw `into` \ tp -> blockOf tp p

block :: Position -> CParser a -> CParser a
block tp p = startBlock tp ..+ hBlock p

blockKw :: LexItem -> CParser a -> CParser a
blockKw kw p = l kw `into` \ tp -> block tp p

hBlock :: CParser a -> CParser a
hBlock p = lc ..+ p +.. rc

-- Must have explicit { }
blockBrOf :: CParser a -> CParser [a]
blockBrOf p = hBlock (sepBy p dsm +.. osm)

pCaseArm :: CParser CCaseArm -- (CPat, [CQual], CExpr)
pCaseArm =  pPat +.+ pOQuals +.+ l L_rarrow ..+ pExpr  >>-
            \ (pattern,(qualifiers,consequent)) ->
                CCaseArm { cca_pattern = pattern,
                           cca_filters = qualifiers,
                           cca_consequent = consequent }

{-
pSummands :: CParser [(Id, CType)]
pSummands = sepBy1 pSummand bar

pSummand :: CParser (Id, CType)
pSummand = pConId +.+ atyp

pField :: CParser (Id, CType)
pField = pFieldId +.+ dc ..+ pType
-}

pQField :: CParser (Id, CQType)
pQField = pFieldId +.+ dc ..+ pQType


-- "{-#" pragmas * "#-}"
pIfcPrags :: CParser [IfcPragma]
pIfcPrags  = l L_lpragma ..+  pIfcPragmas `sepBy` cm +.. l L_rpragma `into`
                  (\a -> succeed $  (concat a))
                  ||! succeed []

prefix :: CParser ()
prefix = literal (mkFString "prefixs") ||| literal (mkFString "prefix")

pIfcPragmas :: CParser [IfcPragma]
pIfcPragmas =
    -- arg_name = [id,id]
    literal (mkFString "arg_names") ..+ eq ..+ lb ..+  varcon `sepBy` cm +.. rb `into`
                (\a -> succeed $  [(PIArgNames a)])
    -- prefix = "str"
    ||!  prefix ..+ eq ..+ varString
             `into` (\x  -> succeed $  [(PIPrefixStr x)])
    -- readys = = [ (id,"str"), ...]
    ||!  literal (mkFString "ready" )  ..+ eq ..+ varString
         `into`  (\x -> succeed $  [(PIRdySignalName x)])
    -- enables = = [ (id,"str"), ...]
    ||!  literal (mkFString "enable")  ..+ eq ..+ varString
         `into`  (\x -> succeed $  [(PIEnSignalName x)])
    -- results = = [ (id,"str"), ...]
    ||!  literal (mkFString "result")  ..+ eq ..+ varString
         `into`  (\x -> succeed $  [(PIResultName x)])
    -- always_ready  or always_enabled
    ||! literal (mkFString "always_ready") .> [PIAlwaysRdy ]
    ||! literal (mkFString "always_enabled") .> [PIAlwaysEnabled ]
    where
        varString = varcon >>- getIdString
        varcon = var ||! con ||! pStringAsId


pQStructField :: CParser CField
pQStructField = pFieldId +.+ dc ..+ pQType +.+ pIfcPrags `into`
                   (\(name,(typ,prags)) ->
                       pClauses name >>-
                       (\cs -> (CField { cf_name = name,
                                         cf_pragmas = if (null prags)
                                                      then Nothing
                                                      else Just prags,
                                         cf_orig_type = Nothing,
                                         cf_default = cs,
                                         cf_type = typ })))

pDefn :: CParser [CDefn]
pDefn = pDefn' >>- (:[]) ||! pData ||! succeed []

pDefns :: CParser [CDefn]
pDefns = ((pDefn `sepBy` sm) >>- concat)

pDefnsAndEOF :: CParser [CDefn]
pDefnsAndEOF =  block noTrig pDefns +.. osm +.. eof

pDefn' :: CParser CDefn
pDefn'   =  pVarDefn
        ||! l L_instance ..+ pQType +.+ l L_where ..+ blockOf noTrig pDefl  >>>   Cinstance
        ||! pTyDefn True
        ||! pPragma                                                         >>-   CPragma

-- parse variable definition
-- XXX backtracks :(
pVarDefn :: CParser CDefn
pVarDefn  =  (pVarId +.+ dc ..+ pQType +.. dsm `into` \(var, typ) -> pClauses1 var >>- CValueSign . CDef var typ)
         ||| (pClauseAny `into` \ (var, clause) -> pClauses var >>- CValue var . (clause :))

pTyDefn :: Bool -> CParser CDefn
pTyDefn b = l L_foreign ..+ pVarId +.+ dc ..+ pQType +.+ opt (eq ..+ pString) +.+ opt (cm ..+ lp ..+ many pString +.+ pForeignRes +.. rp)
                                                                     >>>>> (\ i qt on ops -> Cforeign i qt on ops False)
        ||! l L_primitive ..+ pVarId +.+ dc ..+ pQType                                >>>   Cprimitive
--        ||! l L_primitive ..+ l L_class ..+ pPreds +.+ pTyConIdK +.+ many pTyVarId +.+ pFunDeps        >>>>>  CprimClass
        ||! l L_primitive ..+ l L_type ..+ pTyConId +.+ dc ..+ pKind                >>-  (\ (i, k) -> CprimType (IdKind i k))
        ||! l L_type ..+ pTyConIdK +.+ many pTyVarId +.+ eq ..+ typ0                >>>>  Ctype
        ||! l L_struct ..+ pTyConIdK +.+ many pTyVarId +.+ eql b +.+ blockOf noTrig pQStructField +.+ pDer        >>-
                (\ (ik,(vs,(vis,(fs,der)))) -> Cstruct vis SStruct ik vs fs der)
        ||! l L_interface ..+ pTyConIdK +.+ many pTyVarId +.+ pIfcPrags +.+ eql b  +.+ blockOf noTrig pQStructField +.+ pDer >>-
                (\ (ik,(vs,(ps,(vis,(fs,der))))) -> Cstruct vis (SInterface ps) ik vs fs der)
        ||! l L_class ..+ pOptCoherence +.+ pPreds +.+ pTyConIdK +.+ many pTyVarId +.+ pFunDeps +.+ l L_where ..+ blockOf noTrig pQStructField        >>>>>>>  Cclass

pOptCoherence :: CParser (Maybe Bool)
pOptCoherence = option pCoherence

pCoherence :: CParser Bool
pCoherence = l L_incoherent ..+ succeed True
             ||! l L_coherent ..+ succeed False

pForeignRes :: CParser [String]
pForeignRes = cm ..+ (pString >>- (: []) ||! lp ..+ sepBy1 pString cm +.. rp)

pFunDeps :: CParser CFunDeps
pFunDeps = bar ..+ sepBy1 pFunDep cm
        ||! succeed                                                                []

pFunDep :: CParser ([Id],[Id])
pFunDep = many pTyVarId +.+ l L_rarrow ..+ many pTyVarId

pData :: CParser [CDefn]
pData = pDataB True

pDataB :: Bool -> CParser [CDefn]
pDataB b = l L_data ..+ pTyConIdK +.+ many pTyVarId +.+ eql b +.+ sepBy1 pSummand' bar +.+ pDer         >>- mkData
  where mkData (tik, (vs, (vis, (xs, ids)))) =
            Cdata { cd_visible = vis,
                    cd_name = tik,
                    cd_type_vars = vs,
                    cd_original_summands = map getTs xs,
                    cd_internal_summands = internal_summands,
                    cd_derivings = ids }
                      : if b then concat dss else []
         where  (cs, dss) = unzip (map doCon xs)
                internal_summands =
                    [CInternalSummand { cis_names = constr_names,
                                        cis_arg_type = typ,
                                        cis_tag_encoding = tag_num }
                     | ((constr_names, typ), tag_num) <- zip cs [0..]]
                doCon ([], _) = internalError "CParser.pDataB: no constructor names"
                doCon (constr_names@(first_constr_name:_), x) =
                    ((constr_names, arg), tdef)
                        where ctik = case tik of
                                     IdK ti ->
                                         IdK (mkTCId ti first_constr_name)
                                     IdKind ti k ->
                                         IdKind (mkTCId ti first_constr_name) k
                                     IdPKind ti pk ->
                                         internalError "CParser.pDataB: partial kind"
                              fs = case x of
                                        Left  ts -> zipWith (\ i t -> (setIdPosition (getPosition t) i, t)) tupleIds ts
                                        Right fs -> fs
                              (tdef, arg) =
                                case fs of
                                [] -> ([], cTCon idPrimUnit)
                                [(_, CQType [] t)] | isLeft x -> ([], t)
                                _ -> ([Cstruct True (SDataCon (iKName tik) (not $ isLeft x))
                                         ctik vs
                                         [(CField { cf_name = name,
                                                    cf_pragmas = Nothing,
                                                    cf_orig_type = Nothing,
                                                    cf_default = [],
                                                    cf_type = typ })
                                             | (name,typ) <- fs] ids],
                                       foldl TAp (cTCon (iKName ctik))
                                                 (map cTVar vs))
                getTs (constr_names, Left ts) =
                    COriginalSummand { cos_names = constr_names,
                                       cos_tag_encoding = Nothing,
                                       cos_arg_types = ts,
                                       cos_field_names = Nothing }
                getTs (constr_names, Right its) =
                    COriginalSummand { cos_names = constr_names,
                                       cos_tag_encoding = Nothing,
                                       cos_arg_types = map snd its,
                                       cos_field_names = Just $ map fst its }
                isLeft (Left _) = True
                isLeft (Right _) = False

eql :: Bool -> CParser Bool
eql True = eq .> True
eql False = eqeq .> False ||! eq .> True

pTyConIdK :: CParser IdK
pTyConIdK = pTyConId                                                                >>- IdK
        ||! lp ..+ pTyConId +.+ dc ..+ pKind +.. rp                                >>> IdKind

pKind :: CParser Kind
pKind = pAKind `into` \ k ->  l L_rarrow ..+ pKind                                >>- Kfun k
                          ||! succeed                                               k

pAKind :: CParser Kind
pAKind = star                                                                        .>  KStar
     ||! hash                                                                        .>  KNum
     ||! dollar                                                                      .>  KStr
     ||! lp ..+ pKind +.. rp

pSummandConIds :: CParser [Id]
pSummandConIds = pConId >>- (:[])
               ||! lp ..+ sepBy pConId cm +.. rp

pSummand' :: CParser ([Id], Either [CQType] [(Id, CQType)])
pSummand' = pSummandConIds `into` \ constr_names ->
            blockBrOf pQField                                                >>- (\ fs -> (constr_names, Right fs))
        ||! many atyp                                                        >>- (\ ts -> (constr_names, Left (map (CQType []) ts)))

pDer :: CParser [CTypeclass]
pDer = l L_deriving ..+ lp ..+ sepBy pTypeclass cm +.. rp
   ||! succeed []

opt :: CParser a -> CParser (Maybe a)
opt p = p >>- Just ||! succeed Nothing

pClauses1 :: Id -> CParser [CClause]
pClauses1 i = sepBy1 (pClause i) dsm

pClauses :: Id -> CParser [CClause]
pClauses i = many (dsm ..+ pClause i)

pClause :: Id -> CParser CClause
pClause i = piEq i ..+ many pAPat +.+ pOQuals +.+ eq ..+ exp0           >>>> CClause
        ||! pAPat +.+ psEq i ..+ pAPat +.+ pOQuals +.+ eq ..+ exp0        >>- \ (p1,(p2,(mq,e))) -> CClause [p1,p2] mq e

pClauseAny :: CParser (Id, CClause)
pClauseAny = pVarId +.+ (many pAPat +.+ pOQuals +.+ eq ..+ exp0                >>>> CClause)

pOQuals :: CParser [CQual]
pOQuals =   pQuals                                                        >>- snd
        ||! succeed                                                         []

pQuals :: CParser (Position, [CQual])
pQuals =   l L_when +.+ sepBy1 pQual cm

pQual :: CParser CQual
pQual =  pPat +.+ l L_larrow ..+ pExpr                                        >>> CQGen noType
     ||| pExpr                                                                >>- CQFilter

pRule :: CParser CRule
pRule = many (pRulePragma +.. osm) +.+
        option pLabel +.+ pQuals `into` \ (rps, (ml, (tp, qs))) ->
                l L_drarrow ..+ pExpr                                        >>- CRule rps ml qs
            ||! blockKwOf L_rules pRule                                        >>- CRuleNest rps ml qs

pRules :: CParser [CRule]
pRules = sepBy pRule dsm +.. osm

pLabel :: CParser CExpr
pLabel = aexp +.. l L_colon

piEq :: Id -> CParser Id
piEq i = testp (getIdString i) (\i'->i==i') pVarId

psEq :: Id -> CParser Id
psEq i = testp (getIdString i) (\i'->i==i') pAnySym

pPat :: CParser CPat
pPat = pPatApply ||! pPatOp ||! pAPat

pPatApply :: CParser CPat
pPatApply = pConId `into` (\ c -> blockBrOf pPField                        >>- CPstruct Nothing c
                              ||! many1 pAPat                                >>- CPCon c)

pPatOp :: CParser CPat
pPatOp = binop getFixity mkBinP pConOper pAPat
  where mkBinP p1 op p2 = CPCon op [p1, p2]

{-
pAPat' :: CParser CPat
pAPat' = pConId +.+ blockBrOf pPField                                        >>- (\ (c, fs) -> CPstruct c fs)
     ||! pAPat
-}

pAPat :: CParser CPat
pAPat =     pVarIdOrU `into` (\ mi ->
                                    l L_at ..+ pAPat                        >>- (\ p -> case mi of
                                                                                      Right i -> CPAs i p
                                                                                      Left _ -> p )
                                ||! succeed                                 (case mi of
                                                                               Right i -> CPVar i
                                                                               Left pos -> CPAny pos ))
        ||! pConId                                                        >>- (\i -> CPCon i [])
        ||! lp +.+ sepBy pPat (l L_comma) +.. rp                        >>> pMkTuple
        ||! numericLit                                                        >>- litToPLit
  where
    litToPLit (CLit l) = CPLit l
    litToPLit _ = internalError "CParser.pAPat: litToPLit"

pPField :: CParser (Id, CPat)
pPField = pFieldId `into` \ i ->
                            eq ..+ pPat                                        >>- (\ p -> (i, p))
                        ||! succeed                                        (i, CPVar i)

pPragma :: CParser Pragma
pPragma = l L_lpragma ..+ pPragma'  +.. l L_rpragma
  where pPragma'  = l L_verilog ..+ var +.+ pVeris                        >>- (\ (i, pps) -> Pproperties i (PPverilog : pps))
                ||! l L_synthesize ..+ var +.+ pVeris                        >>- (\ (i, pps) -> Pproperties i (PPverilog : pps))
                ||! properties ..+ var +.+ pProps                        >>> Pproperties
                ||! noinline ..+ many1 var +.. osm                        >>- Pnoinline
        pVeris = optProps pVeriGenProps
        pVeriGenProps = literal (mkFString "noReady") .> PPalwaysReady []        -- deprecated
                    ||! literal (mkFString "alwaysEnabled") .> PPalwaysEnabled []
                    ||! literal (mkFString "parameter") ..+ var >>- PPparam . (\i -> [i])
                    ||! literal (mkFString "no_default_clock") .> PPclock_osc  [(idDefaultClock,"")]
                    ||! literal (mkFString "no_default_reset") .> PPreset_port [(idDefaultReset,"")]
                    ||! literal (mkFString "gate_input_clocks") ..+ eq ..+ l L_lcurl ..+ sepBy varcon cm +.. l L_rcurl >>- PPgate_input_clocks
                    ||! literal (mkFString "clock_family") ..+ eq ..+ l L_lcurl ..+ sepBy varcon cm +.. l L_rcurl >>- PPclock_family
                    ||! literal (mkFString "clock_prefix") ..+ eq ..+ varString >>- PPCLK
                    ||! literal (mkFString "gate_prefix") ..+ eq ..+ varString >>- PPGATE
                    ||! literal (mkFString "reset_prefix") ..+ eq ..+ varString >>- PPRSTN
        pProps = eq ..+ l L_lcurl ..+ sepBy1 pProp cm +.. l L_rcurl
        pProp = literal (mkFString "alwaysReady") .> PPalwaysReady []
            ||! literal (mkFString "noReady") .> PPalwaysReady []                -- deprecated
            ||! literal (mkFString "alwaysEnabled") .> PPalwaysEnabled []
            ||! literal (mkFString "scanInsert") ..+ eq ..+ int >>- PPscanInsert
            ||! literal (mkFString "bitBlast") .> PPbitBlast
            ||! literalC (mkFString "CLK") ..+ eq ..+ varString >>- PPCLK
            ||! literalC (mkFString "RSTN") ..+ eq ..+ varString >>- PPRSTN
            ||! literal (mkFString "options") ..+ eq ..+ l L_lcurl ..+ sepBy varString cm +.. l L_rcurl >>- PPoptions
            ||! l L_verilog .> PPverilog
            ||! l L_synthesize .> PPverilog
            ||! literal (mkFString "deprecate") ..+ eq ..+ varString >>- PPdeprecate
            ||! pVeriGenProps
        properties = literal (mkFString "properties")
        varString = varcon >>- getIdString
        varcon = var ||! con ||! pStringAsId

pRulePragma :: CParser RulePragma
pRulePragma = l L_lpragma ..+ pRulePragma' +.. l L_rpragma
    where pRulePragma' =
                assert ..+
                fire ..+ l L_when ..+ enabled .> RPfireWhenEnabled
             ||! assert ..+ no ..+ implicit ..+ conditions .> RPnoImplicitConditions
             ||! assert ..+ can ..+ schedule ..+ first .> RPcanScheduleFirst
             ||! clock_crossing ..+ rule .> RPclockCrossingRule
             ||! aggressive_implicit_conditions .> RPaggressiveImplicitConditions
             ||! conservative_implicit_conditions .> RPconservativeImplicitConditions
             ||! no_warn .> RPnoWarn
             ||! warn_all_conflicts .> RPwarnAllConflicts
             ||! hide .> RPhide

qvar :: CParser Id
qvar = con +.+ dot ..+ varSym                                                >>> qualId

qcon :: CParser Id
qcon = con +.+ dot ..+ con                                                >>> qualId

qvarop :: CParser Id
qvarop = con +.+ dot ..+ varop                                        >>> qualId

qconop :: CParser Id
qconop = con +.+ dot ..+ conop                                        >>> qualId

pOper :: CParser Id
pOper = pAnySym ||! l L_bquote ..+ pAnyId +.. l L_bquote

pConOper :: CParser Id
pConOper = pConOp ||! l L_bquote ..+ pConId +.. l L_bquote

pAny :: CParser Position
pAny = l L_uscore

pVarId :: CParser Id
pVarId = varSym
      ||! qvar

pVarIdOrU :: CParser (Either Position Id)
pVarIdOrU = pVarId >>- Right
      ||! l L_uscore >>- Left

varSym :: CParser Id
varSym = var ||! lp ..+ pAnySym +.. rp

pHVarId :: CParser Id
pHVarId = (pHidePragma ||! pHideAllPragma) ..+ sm ..+ pVarId     >>- (\ i -> (setHideId i))
      ||! pVarId

piHEq :: Id -> CParser Id
piHEq i = testp (getIdString i) (\i'->i==i') pHVarId             >>- (\ j -> if (isHideId j) then (setHideId i) else i)


-- must not use this for qualifying, or confusion with field names will occur
pModId :: CParser Id
pModId = var ||! con

pConId :: CParser Id
pConId = qcon ||! con

pConOp :: CParser Id
pConOp = qconop ||! conop

pFieldId :: CParser Id
pFieldId = qvar ||! var ||! lp ..+ pAnySym +.. rp

pTyVarId :: CParser Id
pTyVarId = var

pTyConId :: CParser Id
pTyConId = qcon ||! con

-- pAnyId = qvar ||! qcon ||! var ||! con
pAnyId :: CParser Id
pAnyId = pVarId ||! pConId

-- pRuleId = var ||! con

pAnySym :: CParser Id
pAnySym = qvarop ||! qconop ||! varop ||! conop

var :: CParser Id
var = lcp "<var>" (\p x -> case x of
    L_varid fs -> Just (mkId p fs)
    _ -> Nothing)

con :: CParser Id
con = lcp "<con>" (\p x->case x of
    L_conid fs -> Just (mkId p fs)
    _ -> Nothing)

varop :: CParser Id
varop = lcp "<op>" (\p x->case x of
    L_varsym fs -> Just (mkId p fs)
    _ -> Nothing)

conop :: CParser Id
conop = lcp "<op>" (\p x->case x of
    L_consym fs -> Just (mkId p fs)
    _ -> Nothing)

pTyNumId :: CParser CType
pTyNumId = lcp "<integer>" (\p x->case x of
    L_integer _ _ i -> Just (cTNum i p)
    _ -> Nothing)

pTyStrId :: CParser CType
pTyStrId = lcp "<string>" (\p x->case x of
    L_string s -> Just (cTStr (mkFString s) p)
    _ -> Nothing)

literal :: FString -> CParser ()
literal  lfs = lcp (getFString lfs) (\p x->case x of
    L_varid  fs | fs == lfs -> Just ()
    _ -> Nothing)

literalC :: FString -> CParser ()
literalC lfs = lcp (getFString lfs) (\p x->case x of
    L_conid  fs | fs == lfs -> Just ()
    _ -> Nothing)

literalS :: FString -> CParser ()
literalS lfs = lcp (getFString lfs) (\p x->case x of
    L_varsym fs | fs == lfs -> Just ()
    _ -> Nothing)

noinline :: CParser ()
noinline = literal fsNoinline

assert :: CParser ()
assert = literalC fsASSERT

fire :: CParser ()
fire = literal fsFire

enabled :: CParser ()
enabled = literal fsEnabled

no :: CParser ()
no = literal fsNo

implicit :: CParser ()
implicit = literal fsImplicit

conditions :: CParser ()
conditions = literal fsConditions

can :: CParser ()
can = literal fsCan

schedule :: CParser ()
schedule = literal fsSchedule

first :: CParser ()
first = literal fsFirst

clock_crossing :: CParser ()
clock_crossing = literal fsClockCrossing

aggressive_implicit_conditions :: CParser ()
aggressive_implicit_conditions = literal fsAggressiveImplicitConditions

conservative_implicit_conditions :: CParser ()
conservative_implicit_conditions = literal fsConservativeImplicitConditions

no_warn :: CParser ()
no_warn = literal fsNoWarn

warn_all_conflicts :: CParser ()
warn_all_conflicts = literal fsWarnAllConflicts

rule :: CParser ()
rule = literal fsRule

{-
dump :: CParser ()
dump = literal fsDump
  where fsDump = mkFString "dump"
-}

bar :: CParser ()
bar = literalS fsBar

star :: CParser ()
star = literalS fsStar

hash :: CParser ()
hash = literalS fsHash

dollar :: CParser ()
dollar = literalS fsDollar

lt :: CParser ()
lt = literalS fsLT

ltgt :: CParser ()
ltgt = literalS fsLTGT

ltlt :: CParser ()
ltlt = literalS fsLsh

confOp :: CParser ()
confOp = literalS fsConfOp

dotdot :: CParser ()
dotdot = dot ..+ dot .> ()

eqeq :: CParser ()
eqeq = literalS (mkFString "==")

noTrig :: Position
noTrig = mkPosition fsEmpty 0 (-1)

-- Utilities

(>>>>)      :: Parser a (b, (c, d))
            -> (b -> c -> d -> e) -> Parser a e
(>>>>>)     :: Parser a (b, (c, (d, e)))
            -> (b -> c -> d -> e -> f) -> Parser a f
(>>>>>>)    :: Parser a (b, (c, (d, (e, f))))
            -> (b -> c -> d -> e -> f -> g) -> Parser a g
(>>>>>>>)   :: Parser a (b, (c, (d, (e, (f, g)))))
            -> (b -> c -> d -> e -> f -> g -> h) -> Parser a h
--(>>>>>>>>)  :: Parser a (b, (c, (d, (e, (f, (g, h))))))
--            -> (b -> c -> d -> e -> f -> g -> h -> i) -> Parser a i
(>>>>>>>>>) :: Parser a (b, (c, (d, (e, (f, (g, (h, i)))))))
            -> (b -> c -> d -> e -> f -> g -> h -> i -> j) -> Parser a j
p >>>> f = p >>- \ (x,(y,z)) -> f x y z
p >>>>> f = p >>- \ (x,(y,(z,w))) -> f x y z w
p >>>>>> f = p >>- \ (x,(y,(z,(w,a)))) -> f x y z w a
p >>>>>>> f = p >>- \ (x,(y,(z,(w,(a,b))))) -> f x y z w a b
--p >>>>>>>> f = p >>- \ (x,(y,(z,(w,(a,(b,c)))))) -> f x y z w a b c
p >>>>>>>>> f = p >>- \ (x,(y,(z,(w,(a,(b,(c,d))))))) -> f x y z w a b c d

option :: Parser a b -> Parser a (Maybe b)
option p = p >>- Just ||! succeed Nothing

optProps :: CParser a -> CParser [a]
optProps p = l L_lcurl ..+ sepBy p cm +.. l L_rcurl ||! succeed []


eq :: CParser Position
eq = l L_eq
lp :: CParser Position
lp = l L_lpar
rp :: CParser Position
rp = l L_rpar
cm :: CParser Position
cm = l L_comma
dot :: CParser Position
dot = l L_dot
lb :: CParser Position
lb = l L_lbra
rb :: CParser Position
rb = l L_rbra
lc :: CParser Position
lc = l L_lcurl ||! l L_lcurl_o
rc :: CParser Position
rc = l L_rcurl ||! l L_rcurl_o
sm :: CParser Position
sm = l L_semi  ||! l L_semi_o
dc :: CParser Position
dc = l L_dcolon
osm :: CParser Position
osm = sm +.. sm ||! sm ||! succeed noPosition
dsm :: CParser Position
dsm = sm +.. osm
eof :: CParser Position
eof = l L_eof

l :: LexItem -> CParser Position
l li =  token ( \ls->
        case ls of
        Token p li' : ls' -> if li==li' then Right (p, ls') else Left (prLexItem li)
        [] -> internalError "CParser.l: no succeeding token")

getPos :: CParser Position
getPos = token ( \ls->
        case ls of
        Token p _ : _ -> Right (p, ls)
        [] -> internalError "CParser.getPos: no succeeding token")

lcp :: String -> (Position -> LexItem -> Maybe a) -> CParser a
lcp s f =
        token $ \ls->
        case ls of
        Token p li : ls' ->
            case f p li of
            Just x  -> Right (x, ls')
            Nothing -> Left s
        [] -> internalError "CParser.lcp: no succeeding token"

startBlock :: Position -> CParser Bool
startBlock tp@(Position _ _ trigCol _) =
        token $ \ ts ->
        case ts of
        t@(Token p@(Position _ _ c _) li) : ts' | li /= L_lcurl && useLayout ->
             Right (False, Token p L_lcurl_o : rest)
                where rest =
                        if trigCol < c then
                            t : col 0 c ts'
                        else
                            Token p L_rcurl_o : ts
        _ -> Right (True, ts)
  -- insert `;' and `}', but only outside explicit `{ }'
  where col :: Int -> Int -> [Token] -> [Token]
        col l c (t@(Token _ L_lcurl) : ts) = t : col (l+1) c ts
        col l c (t@(Token _ L_rcurl) : ts) = t : col (l-1) c ts
        col 0 c (t@(Token p@(Position _ _ c' _) _) : ts) =
                case compare c' c of
                  LT -> Token p L_rcurl_o : t : ts
                  EQ -> Token p L_semi_o : t : col 0 c ts
                  GT -> t : col 0 c ts
        col 0 c [] = [Token noPosition L_rcurl_o] -- XXX bad position
        col l c (t:ts) = t : col l c ts
        col l c [] = []

errSyntax :: [String] -> [Token] -> EMsg
errSyntax ss ts =
        case ts of
        Token p (L_error le) : _ -> (p, convLexErrorToErrMsg le)
        Token p li           : _ -> (p, ESyntax (showt (prLexItem li)) (map showt (nub ss)))
                where showt t = case show t of
                                    "\"\\\\\"" -> "\"\\\""
                                    s -> s
        [] -> internalError "CParser.errSyntax: no succeeding token"

int :: CParser Integer
int = lcp "<integer>" (\p x->case x of L_integer _ _ i -> Just i; _ -> Nothing)

integer :: CParser CExpr
integer = lcp "<integer>" (\p x->case x of L_integer w b i -> Just (CLit (CLiteral p (LInt (IntLit { ilWidth=w, ilBase=b, ilValue=i })))); _ -> Nothing)
real :: CParser CExpr
real = lcp "<real>" (\p x->case x of L_float r -> Just (CLit (CLiteral p (LReal (fromRational r)))); _ -> Nothing)

numericLit :: CParser CExpr
numericLit = real ||! integer

string :: CParser CExpr
string  = lcp "<string>"  (\p x->case x of L_string  s     -> Just (CLit (CLiteral p (LString s)));  _ -> Nothing)

pString :: CParser String
pString  = lcp "<string>"  (\p x->case x of L_string  s     -> Just s;  _ -> Nothing)

pStringAsId :: CParser Id
pStringAsId = lcp "<string>"  (\p x->case x of L_string  s     -> Just (mkId p (mkFString s));  _ -> Nothing)

char :: CParser CExpr
char = lcp "<char>" (\p x -> case x of L_char c -> Just (CLit (CLiteral p (LChar c))); _ -> Nothing)

hide :: CParser ()
hide = literal fsHide

hideAll :: CParser ()
hideAll = literal fsHideAll

pHidePragma :: CParser ()
pHidePragma = l L_lpragma ..+ hide +.. l L_rpragma

pHideAllPragma :: CParser ()
pHideAllPragma = l L_lpragma ..+ hideAll +.. l L_rpragma
