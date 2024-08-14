{-# LANGUAGE CPP #-}
module CVPrint (
        CPackage(..),
        CSignature(..),
        CExpr(..),
        CType,
        TyVar(..),
        TyCon(..),
        Kind(..),
        CImport(..),
        CQual(..),
        CClause(..),
        CPat(..),
        Literal(..),
        Type(..),
        TISort(..),
        CQType(..),
        CDef(..),
        CExport(..),
        CRule(..),
        CDefn(..),
        CDefl(..),
        CFunDeps,
        CPred(..),
        CFields,
        CStmt(..),
        IdK(..),
        CLiteral(..),
        CMStmt(..),
        COp(..),
        CPOp(..),
        CFixity(..),
        leftCon,
        anyExpr,
        noType,
        iKName,
        impName,
        tMkTuple,
        mkTuple, pMkTuple,
        pvPreds,
        getName,
        getLName,
        isTDef,
        getNK,
        HasPosition(..),
        StructSubType(..),
        pvpId, pvParameterTypes) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.Char(toLower)
import Data.List(genericReplicate)
import Lex(isIdChar)
import PPrint
import PVPrint
import ErrorUtil
import Position(Position, noPosition)
import Id
import IdPrint
import PreStrings (fsAcute)
import PreIds(idPrimUnit, idPrimPair, idIsModule,
              idAction, idActionValue, idPrimSelectFn, id_read)
import CType
import VModInfo
import SchedInfo
import Pragma
import CSyntax
import CSyntaxUtil
import IntLit
import IntegerUtil(integerFormat)
import Util(itos, quote, log2, fromJustOrErr, unconsOrErr)

--------

pp :: (PVPrint a) => PDetail -> a -> Doc
pp d x = pvPrint d 0 x

t :: String -> Doc
t s = text s

--

-- Pretty printing

-- XXX excluded identifiers are commented out because BSV does not support them (yet)
pvpExports :: PDetail -> Either [CExport] [CExport] -> [Doc]
pvpExports d (Right []) = []
pvpExports d (Right excludes) = [ text "/* Do not export (unsupported)" ] ++ map (pp d) excludes ++ [ text "*/" ]
pvpExports d (Left exports) = map (pp d) exports

instance PVPrint CPackage where
    pvPrint d _ (CPackage i exps imps fixs def includes) =
        (t"package" <+> pp d i <> t";") $+$ empty $+$
        pBlockNT d 0 True (pvpExports d exps ++ map (pp d) imps ++ map (pp d) fixs ++ pdefs d def ++ map (pp d) includes) (t"\n") $+$
        (t"endpackage:" <+> pp d i)

pdefs :: PDetail -> [CDefn] -> [Doc]
pdefs _ [] = []
pdefs d (df1@(CPragma (Pproperties i1 props)):df2@(CValueSign (CDef i2 _ _)):rest)
    | i1==i2 =
  (p2defs d df1 df2):(pdefs d rest)
pdefs d dfs@((CPragma (Pnoinline [i1])):(CValueSign (CDef i2 _ _)):_)
    | i1==i2 =
  (t"(* noinline *)") : (pdefs d $ tail dfs)
pdefs d (df:dfs) = (pp d df):(pdefs d dfs)

instance PVPrint CExport where
    pvPrint d p (CExpVar i) = t"export" <+> pvpId d i <> t ";"
    pvPrint d p (CExpCon i) = t"export" <+> pvpId d i <> t ";"
    pvPrint d p (CExpConAll i) = t"export" <+> pvpId d i <> t"(..)" <> t";"
    pvPrint d p (CExpPkg i) = t"export" <+> pvpId d i <> t"::*" <> t";"

instance PVPrint CImport where
    pvPrint d p (CImpId q i) = t"import" <+> pvpId d i <> t "::*" <> t";" <+> ppQualified q
    pvPrint d p (CImpSign _ q (CSignature i _ _ _)) = t"import" <+> pvpId d i <> t "::*" <+> t "...;" <+> ppQualified q

instance PVPrint CInclude where
    pvPrint d p (CInclude i) = t"`include" <+> (doubleQuotes $ t i)

ppQualified :: Bool -> Doc
ppQualified True = text "/* qualified */"
ppQualified False = empty

instance PVPrint CSignature where
    pvPrint d _ (CSignature i imps fixs def) =
        (t"signature" <+> pp d i <+> t "where {") $+$
        pBlock d 0 True (map pi imps ++ map (pp d) fixs ++ map (pp d) def) (t";") (t"}")
      where pi i = t"include" <+> pvpId d i

instance PVPrint CFixity where
    pvPrint d _ (CInfix  p i) = text "`infix"  <+> text (show p) <+> ppInfix d i
    pvPrint d _ (CInfixl p i) = text "`infixl" <+> text (show p) <+> ppInfix d i
    pvPrint d _ (CInfixr p i) = text "`infixr" <+> text (show p) <+> ppInfix d i

pvPreds :: PVPrint a => PDetail -> [a] -> Doc
pvPreds d [] = empty
pvPreds d ps = t "  provisos (" <> sepList (map (pvPrint d 0) ps) (t ",") <> t")"

pvParameterTypeVars :: PDetail -> [Id] -> Doc
pvParameterTypeVars d [] = empty
pvParameterTypeVars d as =
    t"#(" <> sepList (map (\ y -> t"type" <+> pvPrint d 0 y) as) (t ",") <> t ")"

pvParameterTypes :: PDetail -> [Type] -> Doc
pvParameterTypes d [] = empty
pvParameterTypes d ts =
    t"#(" <> sepList (map (\ y -> pvPrint d 0 y) ts) (t ",") <> t ")"

p2defs :: PDetail -> CDefn -> CDefn -> Doc
p2defs d (CPragma (Pproperties _ props))
         (CValueSign df2@(CDef i qt@(CQType ps ty) cs@[CClause cps [] cexp])) | all isVar cps =
      let (ys, x) = getArrows ty
          ity = case x of (TAp (TCon _) y) -> y;
                          (TAp (TVar _) y) -> y;
                          z -> z
          f [] = empty
          f xs = t"#(" <>
                 sepList (zipWith (\ x c -> -- t"parameter" <+>
                                            pvPrint d 0 x <> t"" <+> pvPrint d 10 c)
                                  xs cps)
                 (t",") <> t")"
          (mId,ps') = findModId ps
          line1 = t"module" <+> pvpId d i <> f ys <> t"(" <> pvPrint d 0 ity <> t")"
       in
        if isModule mId x then
         (pProps d props $+$
         (case cexp of
           (Cmodule _ sts) ->
             (pBlockNT d 0 False
              [line1,
               if ps'==[]
               then empty
               else t "  provisos (" <> sepList (map (pvPrint d 0) ps') (t ",") <> t")"] empty)
              <> (t";") $+$
             (pBlock d 2 False (map (pp d) (reorderStmts sts))  empty (t"endmodule:" <+> pp d i))
           e -> (ppValueSignRest d (pvpId d i) ps' True True line1 e "module")))
        else (pProps d props $+$ ppValueSign d i [] qt cs)

p2defs d (CPragma (Pproperties i1 props)) (CValueSign df2@(CDef i2 _ _)) | i1==i2 =
  pProps d props $+$ pvPrint d 0 df2

p2defs d d1 d2 = internalError ("p2defs (" ++ show d1 ++ ")(" ++ show d2 ++ ")")

pProps :: PDetail -> [PProp] -> Doc
pProps _ [] = empty
pProps d ps = t"(*" <+> sepList (map (pvPrint d 0) ps) (text ",") <+> text "*)"

instance PVPrint CDefn where
    pvPrint d p (Ctype i [] ty) =
        sep [t"typedef",
                  nest 2 (pp d ty),
                  pp d i <> t";"]
    pvPrint d p (Ctype i as ty) =
        sep [t"typedef",
                  nest 2 (pp d ty) <+> pp d i <+>
                  pvParameterTypeVars d as <> t ";"]

    pvPrint d p (Cdata { cd_visible = vis,
                         cd_name = i,
                         cd_type_vars = as,
                         cd_original_summands = cs@(_:_),
                         cd_internal_summands = [],
                         cd_derivings = ds }) =  -- a hack to print original constructors
        sep [sep ((t"data1" <+> pp d i) : map (nest 2 . pvPrint d maxPrec) as) <+>
                     t(if vis then "=" else "=="),
                  nest 2 (ppOSummands d cs)]

    pvPrint d p (Cdata { cd_visible = vis,
                         cd_name = i,
                         cd_type_vars = as,
                         cd_internal_summands = cs,
                         cd_derivings = ds }) =
      let typarams = pvParameterTypeVars d as
          ppCon summand = pvPrint d 0 (cis_arg_type summand) <+>
                          pvpId d (getCISName summand) -- XXX print all the names?
          ppIde summand  = pvpId d (getCISName summand) -- XXX print all the names?
          isVoid (CInternalSummand { cis_arg_type = TCon (TyCon unit _ _) }) =
              (unit == idPrimUnit)
          isVoid _ = False
          isEnum = all isVoid
      in
       (if isEnum cs
         then
          t"typedef enum {" $+$
          sepList (map (nest 2 . ppIde) cs) (t",") <> (t"}")
         else
          t"typedef union tagged {" $+$
          pBlock d 4 False (map ppCon cs) (t";") (t"}"))
       <+> pp d i <+> typarams <+> ppDer d ds <> t";"

    pvPrint d p (Cstruct vis (SInterface ps) i [] fs ds) =
        ppIfcPrags d (Just ps) $$
        (t"interface" <+>
         pp d i <> t";" <+> if vis then empty else t"/*") $+$
        pBlock d 4 False (map (ppField d (t"method") True) fs) (t";") (t"endinterface:" <+> pp d i) <+> ppDer d ds
    pvPrint d p (Cstruct vis (SInterface ps) i as fs ds) =
        ppIfcPrags d (Just ps) $$
        (t"interface" <+>
         pvPrint d 9 i <+> pvParameterTypeVars d as
         <> t";" <+> (if vis then empty else t"/*")) $+$
        pBlock d 4 False (map (ppField d (t"method") True) fs)(t";") (t"endinterface:" <+> pp d i) <+> (if vis then empty else t"*/") <+> ppDer d ds


    pvPrint d p (Cstruct vis _ i as fs ds) =
      let typarams = pvParameterTypeVars d as
--          ppCon (i, ty) = pvPrint d 0 ty <+> pvpId d i
      in
        t"typedef struct" <+> t "{" $+$
        pBlock d 4 False (map (ppField d empty False) fs)(t";") (t"} ") <>
        pp d i <+> typarams <+> ppDer d ds <> t";"

{-        (t"typedef struct" <+>
         pp d i <> t(if vis then ";" else "; /*")) $+$
        pBlock d 4 False (map (ppField d "" False) fs)  (t";") (t"}") <+> ppDer d ds
-}

    pvPrint d p (CValueSign def) = pvPrint d p def

    pvPrint d p (Cclass Nothing ps ik is fd ss) =
       ((pBlockNT d 0 False
        [t"typeclass" <+> pp d ik <+> pvParameterTypeVars d is,
         pvpFDs d fd,
         if ps==[]
           then empty
           else t "  provisos (" <> sepList (map (pvPrint d 0) ps) (t",") <> t")"] empty)<> (t";")) $+$
       pBlockNT d 4 False (map (\s -> ppField d (t"function") True s <> t";") ss) empty $+$
       t"endtypeclass"

    pvPrint d p (Cinstance (CQType ps ty) ds) =
      let (x, ys) = unravel ty
      in
       ((pBlockNT d 0 False
        [t"instance" <+> pvPrint d 9 x <> pvParameterTypes d ys,
         if ps==[]
           then empty
           else t "  provisos (" <> sepList (map (pvPrint d 0) ps) (t",") <> t")"] empty)<> (t";")) $+$
       pBlockNT d 4 False (map (pvPrint d 0) ds) empty $+$
       t"endinstance"

    pvPrint d p (Cprimitive i ty) =
        text "primitive" <+> pvpId d i <+> t "::" <+> pp d ty

    pvPrint d p (CPragma pr) = pvPrint d p pr

    pvPrint d p (CprimType (IdKind i k)) =
        t"primitive type" <+> pp d i <+> t "::" <+> pp d k

    pvPrint d p (Cforeign i ty oname opnames _) =
        text "foreign" <+> pvpId d i <+> t "::"
                <+> pp d ty
                <> (case oname of Nothing -> empty; Just s -> text (" = " ++ show s))
                <> (case opnames of
                    Nothing -> empty;
                    Just (is, os) ->
                        t"," <> pparen True (sep (map (text . show) is ++ po os)))
      where po [o] = [text ",", text (show o)]
            po os = [t"(" <> sepList (map (text . show) os) (t",") <> t ")"]

{-
    -- XXX These are not in BSV
    pvPrint d p (CIinstance i qt) =
        t"instance" <+> pvpId d i <> t"" <+> pvPrint d 0 qt
    pvPrint d p (CItype i as usePositions) =
        sep (t"type" <+> pp d i : map (nest 2 . pvPrint d maxPrec) as)

    pvPrint d p (Cclass (Just _) ps ik is fd ss) =

    pvPrint d p (CIclass incoh ps ik is fds usePositions) =
        let pdoc = if ps==[]
                   then empty
                   else t "  provisos (" <>
                        sepList (map (pvPrint d 0) ps) (t",") <> t")"
        in  (pBlockNT d 0 False
              [t"class" <+> pp d ik <+> pvParameterTypeVars d is,
               pvpFDs d fd, pdoc] empty)
            <> (t";")
    pvPrint d p (CIValueSign i ty) = pvpId d i <+> t "::" <+> pp d ty
-}
    pvPrint d p x = internalError ("pvPrint CDefn bad: " ++ show x)

isVar :: CPat -> Bool
isVar (CPVar _) = True
isVar _         = False

getCPVString :: CPat -> String
getCPVString (CPVar i) = getBSVIdString i
getCPVString x = internalError ("getCPVString bad: " ++ show x)

likeModule :: Id -> Bool
likeModule i =
  let s = getIdBaseString i
      ln = length s
      end = drop (ln-6) s
  in if ln > 5 then end=="Module" else False

isModule :: Maybe Id -> Type -> Bool
isModule _ (TAp (TCon (TyCon i _ _)) _) =  likeModule i
isModule (Just i') (TAp (TVar (TyVar i _ _)) _) =  i == i'
isModule _ _          =  False

newIdsn :: Integer -> [String]
newIdsn n = ("x" ++ itos n):(newIdsn (n+1))

newIds :: [Doc]
newIds = map t (newIdsn 1)

isFn :: Type -> Bool
isFn (TAp (TAp (TCon arr) _) _) = isTConArrow arr
isFn _         = False

ppUntypedId :: PDetail -> Doc -> [Doc] -> Doc
ppUntypedId d i ids =
  (t"function") <+> i <> t"(" <> sepList ids (text ",") <> t")"

ppTypedId :: PDetail -> Maybe Id -> Doc -> Type -> [Doc] -> Doc
ppTypedId d mi i y = ppLabelledTypedId d (if isFn y then t"function" else empty) mi (isFn y) i y

ppLabelledTypedId :: PDetail -> Doc -> Maybe Id -> Bool -> Doc -> Type -> [Doc] -> Doc
ppLabelledTypedId d intro modId isFnlike i ty ids =
  let (ys, x) = getArrows ty
      ity = case x of (TAp (TCon _) y) -> y;
                      z -> z
      g [] = empty
      g xs = t"#(" <>  sepList xs (t",") <> t")"
      f [] = intro <+> pp d x <+> i <> (if isFnlike then t"()" else empty)
      f xs = if isModule modId x
              then t"module" <+> i <> g xs <> t"(" <> pvPrint d 0 ity <> t")"
              else intro <+> pvPrint d 9 x <+> i <> t"(" <> sepList xs (text ",") <> t")"
      zs = zipWith (\ y i -> ppTypedId d Nothing i y newIds) ys ids
  in f zs

ppField :: PDetail -> Doc -> Bool -> CField -> Doc
ppField detail intro isFn field =
  let CQType f_provisos f_type = cf_type field
      field_arg_ids = case (cf_pragmas field) of
                      Just f_prags -> map (pvpId detail) argids
                          where argids = filterIArgNames f_prags
                      Nothing -> newIds
      pragmas = ppIfcPrags detail (cf_pragmas field)
      types = ppLabelledTypedId detail intro Nothing isFn
              (pvpId detail (cf_name field)) f_type field_arg_ids
      provisos | null f_provisos = empty
               | otherwise =
                   t "provisos (" <>
                   sepList (map (pvPrint detail 0) f_provisos) (t ",") <>
                   t ")"
      -- XXX there is not BSV syntax for field defaults
  in  pragmas $+$ types $+$ provisos

ppIfcPrags :: PDetail -> Maybe [IfcPragma] -> Doc
ppIfcPrags _ Nothing = empty
ppIfcPrags _ (Just []) = empty
ppIfcPrags d (Just xs) = if (null filtered) then empty else prt
    where filtered = (filterPrintIfcArgs xs)
          prt = t"(*" <+> sep (punctuate comma (map (pvPrint d 0) filtered )) <+> t"*)"

pvpFDs :: PDetail -> CFunDeps -> Doc
pvpFDs d [] = empty
pvpFDs d fd = text "  dependencies" <+> sepList (map (pvpFD d) fd) (t",")

pvpFD :: PDetail -> ([Id], [Id]) -> Doc
pvpFD d (as,rs) = sep (map (pvpId d) as) <+> t "->" <+> sep (map (pvpId d) rs)

{-
ppFDs d [] = t""
ppFDs d fd = text " |" <+> sepList (map (ppFD d) fd) (t",")
ppFD d (as,rs) = sep (map (pvpId d) as) <+> t "->" <+> sep (map (pvpId d) rs)
-}

--ppPreds d [] x = x
--ppPreds d preds x = t "(" <> sepList (map (pvPrint d 0) preds) (t ",") <> t ") =>" <+> x

instance PVPrint IdK where
    pvPrint d p (IdK i) = pvPrint d p i
    pvPrint d p (IdKind i k) = pparen True $ pp d i <+> t "::" <+> pp d k
    pvPrint d p (IdPKind i pk) = pparen True $ pp d i <+> t "::" <+> pp d pk

pBlock :: p -> Int -> Bool -> [Doc] -> Doc -> Doc -> Doc
pBlock d n _ [] _ ket = ket
pBlock d n nl xs sep ket =
        (t (replicate n ' ') <>
        foldr1 ($+$) (map (\ x -> x <> if nl then sep $+$ empty else sep) xs))  $+$
        ket

pBlockNT :: PDetail -> Int -> Bool -> [Doc] -> Doc -> Doc
pBlockNT _ n _ [] _ = empty
pBlockNT _ n nl xs sep =
        (t (replicate n ' ') <>
        foldr1 ($+$) (map (\ x -> x <> if nl then sep $+$ empty else sep) xs))

ppDer :: PDetail -> [CTypeclass] -> Doc
ppDer d [] = empty
ppDer d is = text "deriving (" <> sepList (map (pvPrint d 0) is) (text ",") <> text ")"

--isTerminated (Caction _ _) = True
--isTerminated (Cdo _ _) = True
--isTerminated _ = False

ppMBody :: PDetail -> CExpr -> Doc
ppMBody d e@(Cdo _ _) = pp d e
ppMBody d e@(Caction _ _) = pp d e
ppMBody d e = ppBody d False e

ppMClause :: PDetail -> [Doc] -> CClause -> Doc -> Doc
ppMClause d [x] (CClause ps [] e) mIf | all isVar ps =
       sep [t"method" <+> x <> t"(" <>
                   sepList (map (pvPrint d maxPrec) ps) (t",") <> t")" <+> mIf <+> t";",
            nest 2 (ppMBody d e)]
ppMClause d xs (CClause ps mqs e) mIf =
        sep [t"// APPROXIMATELY:",
                  t"method" <+> sep (xs ++ map (pvPrint d maxPrec) ps) <+> ppQuals d mqs <+> mIf <+> t "=",
                  nest 4 (pp d e)]

ppM :: PDetail -> CDefl -> Doc
ppM d (CLValue i [CClause _ _ (Cinterface _ (Just i1) subIfc)] []) =
    sep ((t"interface"<+>pvpId d i1 <+> pvpId d i <>t";"):
         (map (\ si -> nest 2 (ppM d si)) subIfc) ++
         [t"endinterface:"<+> pvpId d i])
ppM d (CLValue i [cl] me) =
        (ppMClause d [pvpId d i] cl (optIf d me))
        $+$ t"endmethod:" <+> pvpId d i
ppM d (CLValueSign (CDef i _ [cl]) me) =
        (ppMClause d [pvpId d i] cl (optIf d me))
        $+$ t"endmethod:" <+> pvpId d i
ppM d def = pvPrint d 0 def

optIf :: PDetail -> [CQual] -> Doc
optIf _ [] = empty
optIf d qs = t"if (" <> sepList (map (pp d) qs) (t" && ") <> t")"

ppRules :: PDetail -> Int -> [CSchedulePragma] -> [CRule] -> Bool -> Doc
ppRules d p [] rs naked =
  let trs = pBlockNT d 0 False (map (pp d) rs)  empty
  in if naked then trs else (t"rules" $+$ nest 2 trs $+$ t"endrules")

ppRules d p ps rs _ =
  let trs = pBlockNT d 0 False (map (pp d) rs)  empty
  in pPrint d p ps $+$ (t"rules" $+$ nest 2 trs $+$ t"endrules")

ppActions :: PDetail -> CStmts -> Bool -> Doc
ppActions d ss naked =
  let tas = pBlockNT d 0 False (map (pvPrint d 0) ss)  empty
  in if naked then tas else (t"action" $+$ nest 2 tas $+$ t"endaction")

-- findSpecialOps seps a list of operands and operators into two,
-- breaking it at the first "$" operator.  It also gathers operations with
-- operators which are identifiers (and therefore, being user-defined, of
-- highest precedence) into an amalgamated structure of CBinOp's.

findSpecialOps :: [COp] -> ([COp],[COp],Id)
findSpecialOps [] = ([],[],undefined)
findSpecialOps [x] = ([x],[],undefined)
findSpecialOps [x,y] = internalError "bad list of operators and operands"
findSpecialOps ((CRand e1):(CRator _ i):(CRand e2):xs) |
                            (isIdChar (head (getBSVIdString i)) || (getBSVIdString i =="++")) =
  let w = CBinOp e1 i e2
  in findSpecialOps ((CRand w):xs)
findSpecialOps (x:(y@(CRator _ i)):xs) | (getBSVIdString i) == "$" =
  ([x], xs, i)
findSpecialOps (x:y:xs) =
  let (zs,ys,i) = findSpecialOps xs
  in (x:y:zs, ys, i)

ppStrUpd :: PDetail -> CExpr -> [(Id, CExpr)] -> Doc
ppStrUpd d e ies =
  t"(begin let new_struct_ = " <> pvPrint d 0 e <> t";" $+$
  sepList(map (\ (i,e)-> t"  new_struct_."<>pvpId d i<+>t"="<+>pvPrint d 0 e<>t";")ies)empty $+$
  t"new_struct_; end)"

instance PVPrint CExpr where
    pvPrint d p (CLam i e) = ppQuant "\\ "  d p i e
    pvPrint d p (CLamT i ty e) = ppQuant "\\ "  d p i e
    pvPrint d p (Cletrec [] e) = pparen (p > 0) $
        (t"/* empty letseq */" $+$ pp d e)
    --pvPrint d p (Cletrec ds e) = pparen (p > 0) $
    --        (t"let" <+> foldr1 ($+$) (map (pp d) ds)) $+$
    --  (t"in  " <> pp d e)
    pvPrint d p (Cletrec ds e) =
        t "/* letrec */" $+$
        if (p>1) then t"(begin" <+> ppLet <>t";"$+$ t"end)"
                 else if (p==1) then t"begin" <+> ppLet <>t";"$+$ t"end"
                 else ppLet
          where ppLet = ((foldr1 ($+$) (map (pp d) ds)) $+$ pparen True (pp d e))
    pvPrint d p (Cletseq [] e) = pparen (p > 0) $
        (t"let in" <+> pp d e)
    --pvPrint d p (Cletrec ds e) = pparen (p > 0) $
    --        (t"let" <+> foldr1 ($+$) (map (pp d) ds)) $+$
    --  (t"in  " <> pp d e)
    pvPrint d p (Cletseq ds e) =
        if (p>1) then t"(begin" <+> ppLet <>t";"$+$ t"end)"
                 else if (p==1) then t"begin" <+> ppLet <>t";"$+$ t"end"
                 else ppLet
          where ppLet = ((foldr1 ($+$) (map (pp d) ds)) $+$ pparen True (pp d e))
    -- undo ._read desugaring
    pvPrint d p (CSelect e i) | i `qualEq` id_read noPosition = pvPrint d p e
    pvPrint d p (CSelect e i) = pparen (p > (maxPrec+2)) $ pvPrint d (maxPrec+2) e <> t"." <> pvpId d i

--    pvPrint d p (CCon i es) = pparen (p>(maxPrec-1)) $
--        pvpId d i <> t"{" (sepList (map (pp d) es) (t",") ) <> t"}"
--    pvPrint d p (CCon i es) =  pvPrint d p (cVApply i es)
    pvPrint d p (CCon i [p2@(CCon i' _)])|
          getIdString i /= "," && getIdString i' == "," =
       pparen (p>(maxPrec-1)) $ (pvpId d i)<+> pparen True (pp d p2)
    pvPrint d p (CCon i [p2@(CBinOp _ i' _)])|
          getIdString i /= "," && getIdString i' == "," =
       pparen (p>(maxPrec-1)) $ (pvpId d i)<+> pparen True (pp d p2)
    pvPrint d p (CCon i []) = pvpId d i
    pvPrint d p (CCon i as) | getIdString i == "," = ppTuple d as
    pvPrint d p (CCon i as) =
     pparen (p>(maxPrec-1)) $
       (pvpId d i) <+> pparen True (sepList(map (pvPrint d 1) as) (t","))

    pvPrint d p (Ccase pos e arms) =
        if (p>1) then t"(begin" <+> ppCase d e arms $+$ t"end)"
                 else if (p==1) then t"begin" <+> ppCase d e arms $+$ t"end"
                 else ppCase d e arms
    pvPrint d p (CAny {}) = text "?"
    pvPrint d p (CVar i) = pvpId d i
    pvPrint d p (CStruct _ tyc []) | tyc == idPrimUnit = text "()"
    pvPrint d p (CStruct mb tyc ies) =
      pparen (p > 0) $
          mtagged <+> pvPrint d (maxPrec+1) tyc <+> t "{" <+> sepList (map f ies ) (t",") <> t"}"
        where f (i, e) = pvpId d i <+> t ":" <+> pp d e
              mtagged = case mb of
                          Just False -> text "tagged"
                          _ -> empty
    pvPrint d p (CStructUpd e ies) = ppStrUpd d e ies
--        sep (pvPrint d (maxPrec-1) e : map (nest 2 . ppApArg) es)
--      where ppApArg e = pvPrint d maxPrec e
    pvPrint d p (Cwrite pos e v)  = pparen (p > 0) $ pvPrint d (maxPrec+1) e <+> t "<=" <+> pvPrint d p v
    pvPrint d p (CApply (CVar i) [pos, v, idx]) | i == idPrimSelectFn noPosition =
      pvPrint d p (CSub (getPosition pos) v idx)
    pvPrint d p (CApply (CVar i) [CHasType (CVar _) (CQType [] (TAp (TCon _) ty))])
        | getIdBaseString i == "primValueOf"
      = pparen (p>(maxPrec-1)) $ t"valueOf" <> pparen True (pp d ty)

    pvPrint d p (CApply (CVar i)
                 [CHasType the_lit@(CLit (CLiteral _
                                          ( LInt (IntLit w b v))))
                  (CQType [] (TAp (TCon (TyCon i2 _ _)) (TCon (TyNum nTy _))))])
          | getIdBaseString i == "unpack" && getIdBaseString i2 == "Bit"
      = (t $ show nTy) <> (pp d the_lit)

    pvPrint d p (CApply e@(CVar _) es) = pparen (p>(maxPrec-1)) $
        pp d e <> pparen True (sepList (map (pvPrint d 1) es) (t",") )
    pvPrint d p (CApply e es) = pparen (p>(maxPrec-1)) $
        pparen True (pp d e) <> pparen True (sepList (map (pvPrint d 1) es) (t",") )
    pvPrint d p (CTaskApply e es) = pparen (p>(maxPrec-1)) $
        pp d e <> pparen True (sepList (map (pvPrint d 1) es) (t",") )
    pvPrint d p (CTaskApplyT e tt es) = pparen (p>(maxPrec-1)) $
        pp d e <> pparen True (sepList (map (pvPrint d 1) es) (t",") )
    pvPrint d p (CLit l) = pvPrint d p l
    pvPrint d p (CBinOp e1 i e2) = ppOp d p i e1 e2
    pvPrint d p (CHasType e t) = pparen (p>0) $
        pvPrint d maxPrec t <> text "'" <> (pparen True $ pp d e)
    pvPrint d p (Cif pos c tr e) = pparen (p>0) (sep [pvPrint d 1 c <+> t "?", nest 4 (pvPrint d 1 tr), t":", nest 4 (pvPrint d 1 e)])
    pvPrint d p (CSub pos e s) = pvPrint d maxPrec e <> t"[" <> pp d s <> t"]"
    pvPrint d p (CSub2 e h l) = pvPrint d maxPrec e <> t"[" <> pp d h <> t":" <> pp d l <> t"]"
    -- XXX not valid BSV
    pvPrint d p (CSubUpdate pos e_vec (e_h, e_l) e_rhs) = pvPrint d p (CSub2 e_vec e_h e_l) <> t"=" <> pvPrint d p e_rhs
    pvPrint d p (Cmodule _ is) =
     t"module " $+$ pBlock d 2 False (map (pp d) (reorderStmts is)) empty (t"endmodule")
--  pvPrint d p (Cinterface Nothing ds) =
--        (t"interface {" $+$ pBlock d 2 False (map (pp d) ds) (t";") (t"}"))
    pvPrint d p (Cinterface pos Nothing ds) =
        (pBlockNT d 0 False (map (ppM d) ds) empty)
--    pvPrint d p (CLValueSign def me) = optWhen d me $ pvPrint d p def
    pvPrint d p (Cinterface pos (Just i) ds) =
        (t"interface" <+> pp d i) $+$
        (pBlock d 2 False (map (ppM d) ds)  empty (t"endinterface:" <+> pp d i))
    pvPrint d p (CmoduleVerilog m ui c r ses fs sch ps) =
        sep [
          t"(unexpected) module verilog" <+> pp d m <> t";",
          (if c==(ClockInfo [][][][]) then empty else pPrint d p c),
          (if r==(ResetInfo [][]) then empty else pPrint d p r),
          nest 4 (if null ses then empty else pparen True (sepList (map ppA ses) (t","))),
          nest 4 (t"{" $+$ pBlock d 2 False (map (ppVeriMethod d Nothing) fs) (t";") (t"}")),
          nest 4 (pp d sch),
          nest 4 (pp d ps) ]
          where ppA (s, e) = text "(" <> text (show s) <> text "," <+> pp d e <> text ")"
    pvPrint d p (CForeignFuncC i wrap_ty) =
        t"(unexpected) ForeignFuncC" <+> pp d i
    pvPrint d p (Cdo _ ss) = pparen (p>0) $ t "actionvalue" $+$ nest 2 (ppActions d ss True) $+$ t "endactionvalue"
    pvPrint d p (Caction _ ss) = pparen (p>0) $ ppActions d ss False
    pvPrint d p (Crules ps rs) = ppRules d p ps rs False
    ----
    pvPrint d p (COper []) = empty
    pvPrint d p (COper [(CRand p1)]) = pvPrint d p p1
    pvPrint d p (COper [(CRand p1), (CRator _ i), (CRand p2)])
      = ppOp d p i p1 p2
    pvPrint d p (COper ops) =
      let (ys,zs,i) = findSpecialOps ops
      in if (null zs) then pparen (p > maxPrec-1) (sep (map (pvPrint d (maxPrec-1)) ys))
         else ppOp d p i (COper ys) (COper zs)
    ----
    pvPrint d p (CCon1 _ i e) = pvPrint d p (CCon i [e])
    pvPrint d p (CSelectTT _ e i) = pvPrint d p (CSelect e i)
    ----
    pvPrint d p (CCon0 _ i) = pvpId d i
    ----
    pvPrint d p (CConT _ i es) = pvPrint d p (CCon i es)
    pvPrint d p (CStructT ty ies) = pvPrint d p (CStruct (Just True) tyc ies)
        where tyc = fromJustOrErr "pvPrint CStructT" (leftCon ty)
    pvPrint d p (CSelectT _ i) = text "." <> pvpId d i
    pvPrint d p (CLitT _ l) = pvPrint d p l
    pvPrint d p (CAnyT pos uk t) = text "?"
    pvPrint d p (CmoduleVerilogT _ m ui c r ses fs sch ps) =
        pvPrint d p (CmoduleVerilog m ui c r ses fs sch ps)
    pvPrint d p (CForeignFuncCT i prim_ty) =
        t"(unexpected) ForeignFuncC" <+> pp d i
    pvPrint d p (CTApply e ts) = pparen (p>(maxPrec-1)) $
        sep (pvPrint d (maxPrec-1) e : map (nest 2 . ppApArg) ts)
        where ppApArg ty = t"\183" <> pvPrint d maxPrec ty
    pvPrint d p (Cattributes pps) =
        text "Attributes" <> pparen True (pvPrint d 0 (map snd pps))
--    pvPrint d p x = internalError ("pvPrint CExpr bad: " ++ show x)

instance PVPrint CLiteral where
    pvPrint d p (CLiteral _ l) = pvPrint d p l

isInstantiating :: CExpr -> Bool
isInstantiating (CApply (CVar i) es)  | take 2 (getIdBaseString i) == "mk" = True
isInstantiating (CVar i)  | take 2 (getIdBaseString i) == "mk" = True
isInstantiating _ = False

separgs :: PDetail -> CExpr -> (Doc, Doc)
separgs d (CApply e es) = (pp d e,
        t"#(" <> sepList (map (pp d) es) (t",") <>t")" )
separgs d e = (pp d e, empty)

instance PVPrint CStmt where
    pvPrint d p (CSBindT (CPVar i) maybeInstName pprops (CQType _ ty) e) =
      let -- (tx, tys) = unravel ty
          (ep, argsp) = separgs d e
          instName = case maybeInstName of
                     Just name -> pp d name
                     Nothing -> text "the_" <> pp d i
          isInst = isInstantiating e
      in
        foldr ($+$) empty (map (pvpPProp d . snd) pprops) $+$
        (pp d ty <> t"" <+> pp d i <> t(if isInst then "();" else ";")) $+$
        (if isInst
          then ep <> {- f tys <> -} argsp <+> instName <> t"(" <> pp d i <> t");"
          else pp d i <+> t "<-" <+> pp d e <> t";")

    pvPrint d p (CSBindT pat _ pprops ty e) =
        foldr ($+$) empty $
            (map (pvpPProp d . snd) pprops) ++
            [pp d ty <+> pp d pat <+> t "<-" <+> pp d e <> t";"]
    pvPrint d p (CSBind pat _ pprops e) =
        foldr ($+$) empty $
            (map (pvpPProp d . snd) pprops) ++
            [t"let" <+> pp d pat <+> t "<-" <+> pp d e <> t";"]
    pvPrint d p (CSletrec ds) = foldr1 ($+$) (map (pp d) ds)
    pvPrint d p (CSletseq ds) = foldr1 ($+$) (map (pp d) ds)
    pvPrint d p (CSExpr _ e@(Ccase _ _ _)) = pvPrint d p e
    pvPrint d p (CSExpr _ e) = pvPrint d (p+2) e <> t";"

isIfce :: CMStmt -> Bool
isIfce (CMinterface _) = True
isIfce (CMTupleInterface _ _) = True
isIfce _ = False

reorderStmts :: [CMStmt] -> [CMStmt]
reorderStmts stmts = [x | x <- stmts, not(isIfce x)] ++ [x | x <- stmts, isIfce x]

instance PVPrint CMStmt where
    pvPrint d p (CMStmt (CSExpr _ (CApply (CVar i) [Crules ps rs])))
        | getIdBaseString i == "addRules"
      = ppRules d p ps rs True
    pvPrint d p (CMStmt (CSExpr _ (COper [CRand (CVar i), CRator _ i', CRand (Crules ps rs)])))
        | getIdBaseString i == "addRules" && getIdBaseString i' == "$"
      = ppRules d p ps rs True
    pvPrint d p (CMStmt s) = pvPrint d p s
    pvPrint d p (CMrules (Crules ps rs)) = ppRules d p ps rs True
    pvPrint d p (CMrules e) = pvPrint d p e
    pvPrint d p (CMinterface (Cinterface pos (Just _) e )) = pvPrint d p (Cinterface pos Nothing e)
    pvPrint d p (CMinterface e) = pvPrint d p e
    pvPrint d p (CMTupleInterface _ es) =
        let n = length es
        in t ("return(tuple"++show n++"(") <>
            sepList (map (pvPrint d p) es) (text ",") <> text "));"

instance PVPrint COp where
    pvPrint d pn (CRand p) = pvPrint d pn p
    pvPrint d _ (CRator _ i) = ppInfix d i

ppQuant :: String -> PDetail -> Int -> Either Position Id -> CExpr -> Doc
ppQuant s d p ei e =
    let ppI (Left _) = text ".*"
        ppI (Right i) = pvPrint d 0 i
    in  pparen (p>0) (sep [t s <> ppI ei <+> t "->", pp d e])

ppCaseBody :: PDetail -> CExpr -> Doc
ppCaseBody d e@(CApply (CVar i) _) | getIdBaseString i == "return"  = pparen False (pp d e)
ppCaseBody d e = pparen True (pvPrint d 1 e)

ppCase :: PDetail -> CExpr -> [CCaseArm] -> Doc
ppCase detail scrutinee arms =
    (t"case" <+> pparen True (pvPrint detail 1 scrutinee) <+> t "matches") $+$
    pBlock detail 0 False (map ppArm arms) empty (t"endcase")
  where ppArm arm =
         sep [ppPat (cca_pattern arm) <+>
              ppQuals detail (cca_filters arm) <+> t ": ",
              nest 2 (ppCaseBody detail (cca_consequent arm))] <> t";"
        ppPat pt = pp detail pt

findPs :: CExpr -> [CExpr]
findPs (CBinOp e1 i e2) | getBSVIdString i == "," = e1:(findPs e2)
findPs e = [e]

ppTuple :: PDetail -> [CExpr] -> Doc
ppTuple d es =
  let n = length es
  in t("tuple" ++ show n) <> pparen True (sepList (map (pvPrint d 1) es) (t","))

ppOp :: PDetail -> Int -> Id -> CExpr -> CExpr -> Doc
ppOp d pd i p1 p2 =
  let rand1 = pvPrint d 1 p1
      rand2 = pvPrint d 1 p2
      ppr = pparen (pd > 2) -- to distinguish from (_?_:_)
  in
      (case getBSVIdString i of
        "," -> let ps = p1:(findPs p2)
               in ppTuple d ps
        "$" -> ppr (case p1 of
                    (CApply e es) -> pvPrint d 0 (CApply e (es++[p2]))
                    (CCon i es) -> pvPrint d 0 (CCon i (es++[p2]))
                    _ -> rand1 <> pparen True rand2
                  )
        "++" -> t"{" <> sepList (map (pvPrint d 0) [p1,p2]) (t",") <> t"}"
        "<+" -> ppr(t "preempts" <> pparen True (sep [ rand1 <> t",", rand2]))
        "+>" -> ppr(t "preempted" <> pparen True (sep [ rand1 <> t",", rand2]))
        "<->" -> ppr(t "mkConnection" <> pparen True (sep [ rand1 <> t",", rand2]))




        s@(c:_) | isIdChar c -> ppr(t s <> pparen True (sep [ rand1 <> t",", rand2]))
        _                    -> ppr(sep [rand1 <> t"" <+> ppInfix d i, rand2])
      )

ppRQuals :: PDetail -> [CQual] -> Doc
ppRQuals d [] = empty
ppRQuals d qs = t"(" <> sepList (map (pp d) qs) (t" && ") <> t");"

ppQuals :: PDetail -> [CQual] -> Doc
ppQuals d [] = empty
ppQuals d qs = t"&&&" <+> sepList (map (pp d) qs) (t" && ")

ppOSummands :: PDetail -> [COriginalSummand] -> Doc
ppOSummands d cs = sepList (map (nest 2 . ppOCon) cs) (t"; ")
  where ppOCon summand =
            sep (pvpId d (getCOSName summand) -- XXX print all the names?
                 : map (pvPrint d maxPrec) (cos_arg_types summand))

--ppSummands d cs = sepList (map (nest 2 . ppCon) cs) (t"; ")
--  where ppCon (i, t) = pvPrint d maxPrec t <> pvpId d i

{-
ppVeriPort d (s, []) = t s
ppVeriPort d (s, prs) = t s <> t"{" <> sepList (map (pvPrint d 0) prs) (t",") <> t"}"
-}

ppVeriArg :: PDetail -> (VArgInfo, CExpr) -> Doc
ppVeriArg d (Param (VName s), e) = t("parameter " ++ s ++ " = ")<> pvPrint d 0 e
ppVeriArg d (Port ((VName s), pps) mclk mrst, e) =
    let clk_name = case mclk of
                       Nothing  -> t "no_clock"
                       Just clk -> pvPrint d 0 clk
        rst_name = case mrst of
                       Nothing  -> t "no_reset"
                       Just clk -> pvPrint d 0 clk
    in  t "port" <+> ppPortProps d pps <> t s <+>
        t "clocked_by (" <> clk_name <> t ")" <+>
        t "reset_by (" <> rst_name <> t ")>" <+>
        t "=" <+> pvPrint d 0 e
ppVeriArg d (ClockArg i, e)  = t"clock " <> pvpId d i <> t" = " <> pvPrint d 0 e
ppVeriArg d (ResetArg i, e)  = t"reset " <> pvpId d i <> t" = " <> pvPrint d 0 e
ppVeriArg d (InoutArg (VName s) mclk mrst, e) =
    let clk_name = case mclk of
                       Nothing  -> t "no_clock"
                       Just clk -> pvPrint d 0 clk
        rst_name = case mrst of
                       Nothing  -> t "no_reset"
                       Just clk -> pvPrint d 0 clk
    in  t "inout" <+> t s <+>
        t "clocked_by (" <> clk_name <> t ")" <+>
        t "reset_by (" <> rst_name <> t ")>" <+>
        t "=" <+> pvPrint d 0 e

ppVeriMethod :: PDetail -> Maybe VPort -> VFieldInfo -> Doc
ppVeriMethod d _  (Clock i) = t"clock " <> pvpId d i
ppVeriMethod d _  (Reset i) = t"reset " <> pvpId d i
ppVeriMethod d _  (Inout i (VName s) mclk mrst) =
  t"ifc_inout" <+> (pvpId d i) <+> t ("(" ++ s ++ ")") <+>
  (case mclk of
     Nothing -> empty
     Just i -> t"clocked_by (" <> pvpId d i <> t")") <+>
  (case mrst of
     Nothing -> empty
     Just i -> t"reset_by (" <> pvpId d i <> t")")
ppVeriMethod d mr (Method i mc mreset n pts mo me) =
  let f _ _ Nothing = empty
      f before after (Just (VName vn, prs)) =
         (case prs of
          [] -> empty
          xs -> t"(*" <+> sepList (map (pvPrint d 0) xs) (t ",") <> t" *) ") <>
         (t (before ++ vn ++ after))
  in
   t"method " <>
   (f "" " " mo) <>
   (pvpId d i <>
   (if n == 1 then empty else (t"[" <> (pp d n) <> t"]")) <>
   (t"(" <> sepList (map (f "" "" . Just) pts) (t",") <> t")") <>
   (f " enable (" ")" me) <>
   (f " ready ("  ")" mr) <>
   (case mc of
     Nothing -> empty
     Just i -> t" clocked_by (" <> pvpId d i <> t")") <>
   (case mreset of
     Nothing -> empty
     Just i -> t" reset_by (" <> pvpId d i <> t")"))

ppPortProps :: PDetail -> [VeriPortProp] -> Doc
ppPortProps d [] = empty
ppPortProps d (vp:vpps) =
    text "(* " <> pvPrint d 0 vp <> text " *) " <> ppPortProps d vpps

instance PVPrint CDef where
    pvPrint d p (CDefT i vs ty cs) = ppValueSign d i vs ty cs

    -- XXX this seems out of date with the BSV parser
    pvPrint d p (CDef i (CQType ps ty) [CClause cps []
        (CmoduleVerilog m ui c r args meths sch pts)]) | all isVar cps =
      let (ys, x) = getArrows ty
          ity = case x of (TAp (TCon _) y) -> y;
                          z -> z
          s (CLit (CLiteral _ (LString x))) = x
          s x = internalError ("pvPrint CDef not lit: " ++ show x)
          f [] = empty
          f xs = t"#(" <>
                 sepList (zipWith (\ x c -> -- t"parameter" <+>
                                            pvPrint d 0 x <> t"" <+> pvPrint d 10 c)
                                  xs cps)
                 (t",") <> t")"
          pOutMClk Nothing = empty
          pOutMClk (Just ((VName s), mg)) = t s <> pOutMGate mg
          pOutMGate Nothing = empty
          pOutMGate (Just (VName s, vpps)) = t", " <> ppPortProps d vpps <> t s
          pInMClk Nothing = empty
          pInMClk (Just ((VName s), mg)) = t s <> pInMGate mg
          -- these technically need a placeholder gate name (CLK_GATE?)
          pInMGate (Left True) = empty -- text ", (* inhigh *)"
          pInMGate (Left False) = text ", (* unused *)"
          pInMGate (Right (VName s)) = t", " <> t s
          noInputResets = null (input_resets r)
          (mId,ps') = findModId ps
       in (if isModule mId x -- xxx readies xxx
           then
           (((pBlockNT d 0 False
              [t"import \"BVI\"" <+> t(s m) <>
               t" = module" <+> pvpId d i <> f ys <> t"(" <> pvPrint d 0 ity <> t")",
               if ps'==[]
               then empty
               else t "  provisos (" <> sepList (map (pvPrint d 0) ps') (t ",") <> t")"] empty)
             <> (t";")) $+$
            (pBlock d 2 False
             ((let ClockInfo in_cs out_cs as ss = c
               in ((map (\ (i, mc) ->
                         -- we could print this as "input_clock" if we want
                         t"clock" <+> pp d i <+> t"(" <> pOutMClk mc <> t")") out_cs) ++
                   (map (\ (i, mc) ->
                         -- we could print this as "output_clock" if we want
                         t"clock" <+> pp d i <+> t"(" <> pInMClk mc <> t")") in_cs) ++
                   (map (\ (i1, i2) -> t"ancestor" <+> pp d i1 <>t","<+> pp d i2) as) ++
                   (map (\ (i1, i2) -> t"sibling" <+> pp d i1 <>t","<+> pp d i2) ss))) ++
              (if noInputResets then [t"no_reset"] else []) ++
              (map (pPrint d p) (input_resets r)) ++ -- XXX is this right?
              (map (pPrint d p) (output_resets r)) ++ -- XXX is this right?
              (map (ppVeriArg d) args) ++
              (map (ppVeriMethod d Nothing) meths) ++
              (ppSchedInfo d p sch) ++
              [ppPathInfo d p pts])
             (t";")
             (t"endmodule:" <+> pp d i)))
           else t "ERROR (for verilog module): module not of module type"
          )

    -- for bsc2bsv, if CForeignFuncC is ever supported in Classic
    pvPrint d p (CDef bsv_id cqt [CClause [] [] (CForeignFuncC c_id _)]) =
      t"import \"BDPI\"" <+>
      (if (bsv_id == c_id)
       then empty
       else t (getIdString c_id) <+> t "="
      ) <+>
      ppField d (t"function") True (CField bsv_id Nothing cqt [] Nothing) <> t";" $+$
      t"endfunction"

    pvPrint d p df@(CDef i (CQType _ _) [CClause cps [] _]) | all isVar cps =
      p2defs d (CPragma (Pproperties i [])) (CValueSign df)

    pvPrint d p (CDef  i    ty cs) = ppValueSign d i [] ty cs

ppPathInfo :: PDetail -> Int -> VPathInfo -> Doc
ppPathInfo d p ps = pPrint d p ps

instance PVPrint VPathInfo where
    pvPrint d p v = ppPathInfo d p v

ppSchedInfo :: PDetail -> Int -> VSchedInfo -> [Doc]
ppSchedInfo d p (SchedInfo mci rms rbm ccm) =
    let ds = makeMethodConflictDocs (pvPrint d p) pvpReadable "(" ")" mci
        mci_docs = map (\x -> text "schedule" <+> x) ds
        rms_docs = map (\p -> text "rule_between" <+> pvPrint d 0 p) rms
        rbm_docs = map (\p -> text "rule_before" <+> pvPrint d 0 p) rbm
        ccm_docs = map (\p -> text "cross-domain" <+> pvPrint d 0 p) ccm
    in  mci_docs ++ rms_docs ++ rbm_docs ++ ccm_docs

ppBodyLets :: PDetail -> [CDefl] -> Doc
ppBodyLets d [] = empty
ppBodyLets d (d1:ds) =
   t"  " <> pp d d1 $+$ ppBodyLets d ds

ppBody :: PDetail -> Bool -> CExpr -> Doc
ppBody d isMod (Cletrec [CLValueSign (CDef i1 t1 c1) q1]
                (Cletrec [CLValueSign (CDef i2 _ _) _] e))
                         | i1 == mkIdPost i2 fsAcute =
        ppBodyLets d [CLValueSign (CDef i2 t1 c1) q1] $+$
        (ppBody d isMod e)
ppBody d isMod (Cletrec ds e) =
        ppBodyLets d ds $+$
        (ppBody d isMod e)
ppBody d True e = (pparen True (pp d e) <> t";")
ppBody d _ e = (t"  return" <+> pparen True (pvPrint d 1 e) <> t";")

findModId :: [CPred] -> (Maybe Id, [CPred])
findModId [] = (Nothing,[])
findModId (p:ps) =
   case p of
     (CPred (CTypeclass isM) [TVar (TyVar iM _ _), _]) | getIdBaseString isM == getIdBaseString idIsModule
       -> (Just iM,ps)
     _ -> let (i,ps') = findModId ps in (i,p:ps')

ppValueSignRest :: PDetail -> Doc -> [CPred] -> Bool -> Bool -> Doc -> CExpr -> String -> Doc
ppValueSignRest d i ps isFnT isMod line1 cexp ender =
   ((pBlockNT d 0 False
        [line1,
         if ps==[]
           then empty
           else t "  provisos (" <> sepList (map (pvPrint d 0) ps) (t",") <> t")"] empty)<> (t";")) $+$
   (if isFnT then
                (ppBody d isMod cexp $+$ t ("end"++ender++":") <+> i)
               else (i <+> t "=" <+> pvPrint d 2 cexp <> t ";"))

ppValueSign :: PDetail -> Id -> [TyVar] -> CQType -> [CClause] -> Doc

ppValueSign d i [] (CQType ps ty) [CClause cs [] cexp] | all isVar cs =
  let id = pvpId d i
      (modId,ps') = findModId ps
      line1 = ppTypedId d modId id ty (map (t . getCPVString) cs)
  in ppValueSignRest d id ps' (isFn ty) False line1 cexp "function"

ppValueSign d i [] ty cs =
        (pvpId d i <+> t "::" <+> pp d ty <> t";") $+$
        foldr1 ($+$) (map (\ cl -> ppClause d [pvpId d i] cl) cs)
ppValueSign d i vs ty cs =
        (pvpId d i <+> t ":: /\\" <> sep (map (pvPrint d maxPrec) vs) <> t"." <> pp d ty <> t";") $+$
        foldr1 ($+$) (map (\ cl -> ppClause d [pvpId d i] cl) cs)

ppRuleBody :: PDetail -> CExpr -> Doc
ppRuleBody d (Cletrec ds (Caction _ ss)) =
           (foldr1 ($+$) (map (pp d) ds)) $+$ ppActions d ss True
ppRuleBody d (Caction _ ss) = ppActions d ss True
ppRuleBody d e              = pp d e <> t";"

ppRuleName :: PDetail -> Maybe CExpr -> Doc
ppRuleName d Nothing = t"dummy_name"
ppRuleName d (Just(CLit(CLiteral _ (LString s)))) = t(f s) where
   f s = map (\ c -> if c==' ' then '_' else c) ((toLower (head s)):(tail s))
ppRuleName d (Just i) = pp d i

instance PVPrint CRule where
    pvPrint d p (CRule [] mlbl mqs e) =
            (t"rule" <+> ppRuleName d mlbl) <+> ppRQuals d mqs $+$
             nest 3 (ppRuleBody d e) $+$
            (case mlbl of Just _ -> t "endrule:" <+> ppRuleName d mlbl;
                          _ -> t"endrule")

    pvPrint d p (CRule rps mlbl mqs e) =
            ppRPS d rps $+$
            (t"rule" <+> ppRuleName d mlbl) <+> ppRQuals d mqs $+$
             nest 3 (ppRuleBody d e) $+$
            (case mlbl of Just _ -> t "endrule:" <+> ppRuleName d mlbl;
                          _ -> t"endrule")

    pvPrint d p (CRuleNest rps mlbl mqs rs) =
            ppRPS d rps $+$ t"rule" <+> ppRuleName d mlbl <+>
              (ppQuals d mqs $+$ pBlock d 2 False (map (pp d) rs) (t";") (t"endrule"))

ppRPS :: PDetail -> [RulePragma] -> Doc
ppRPS _ [] = empty
ppRPS _ rps = t"(*" <+> sepList (map ppRP rps) (t",") <+> t "*)"

ppRP :: RulePragma -> Doc
ppRP RPfireWhenEnabled                = t"fire_when_enabled"
ppRP RPnoImplicitConditions           = t"no_implicit_conditions"
ppRP RPaggressiveImplicitConditions   = t"aggressive_implicit_conditions"
ppRP RPconservativeImplicitConditions = t"conservative_implicit_conditions"
ppRP RPnoWarn                         = t"no_warn"
ppRP RPwarnAllConflicts                  = t"warn_all_conflicts"
ppRP RPcanScheduleFirst               = t"can_schedule_first"
ppRP RPclockCrossingRule              = t"clock_crossing_rule"
ppRP (RPdoc comment)                  = t ("doc = " ++ quote comment)
ppRP RPhide                           = t"hide"

--unmkTuple :: CExpr -> [CExpr]
--unmkTuple (CBinOp e i es) | getIdBaseString i == "," =
--  let bs = unmkTuple es
--  in e:bs
--unmkTuple x = [x]

pUnmkTuple :: CPat -> [CPat]
pUnmkTuple (CPCon i [e,es]) | getIdBaseString i == "," =
  let bs = pUnmkTuple es
  in e:bs
pUnmkTuple x = [x]

instance PVPrint CDefl where
    pvPrint d p (CLValueSign def me) = optWhen d me $ pvPrint d p def
    pvPrint d p (CLValue i cs me) = optWhen d me $
        foldr1 ($+$) (map (\ cl -> ppClause d [pvpId d i] cl) cs)
--    pvPrint d p (CLMatch ps@(CPCon i _) e) | getIdBaseString i == "," =
--        t "match {" <> (catList(map (pvPrint d maxPrec) (pUnmkTuple ps)) (t","))<>t"} =" $+$
--                  nest 4 (pp d e) <> t";"
    pvPrint d p (CLMatch pat e) =
        t"match"<+> pp d pat <+> t"=" $+$
                  nest 4 (pp d e) <> t";"

optWhen :: PDetail -> [CQual] -> Doc -> Doc
optWhen d [] s = s
optWhen d qs s = s $+$ (t"    " <> ppQuals d qs)

instance PVPrint CClause where
    pvPrint d p cl = ppClause d [] cl

ppClause :: PDetail -> [Doc] -> CClause -> Doc
ppClause d xs (CClause [] mqs e) =
        sep [t"let" <+> sep xs <> ppQuals d mqs <+> t "= ",
                  nest 4 (pp d e)]
        <> t";"
ppClause d xs (CClause ps [] e) =
    let ids' = xs ++ map (ppCP d) ps
        (i, ids) = unconsOrErr "CVPrint.ppClause" ids'
        line1 = ppUntypedId d i ids
    in ppValueSignRest d i [] True False line1 e "function"

ppClause d xs (CClause ps mqs e) =
    internalError ("CClause: "++ show (ps,mqs,e))

ppCP :: PDetail -> CPat -> Doc
ppCP d p =
    case pUnmkTuple p of
     [x] -> pp d x
     xs  -> t"{"<>(catList(map (pp d) xs) (t","))<>t"}"

instance PVPrint CQual where
        pvPrint d p (CQGen _ pattern expr) =
            pp d expr <+> t "matches" <+> pp d expr
        pvPrint d p (CQFilter e) = pp d e


instance PVPrint CPat where
    pvPrint d p (CPVar i) = pvpPId d i

    pvPrint d p (CPCon i [p2@(CPCon i' _)])|
          getIdString i /= "," && getIdString i' == "," =
       pparen (p>(maxPrec-1)) $ (t"tagged" <+> pvpId d i)<+> pp d p2


    pvPrint d p (CPCon i []) =
       pparen (p>(maxPrec-1)) (t"tagged" <+> pvpId d i)

    pvPrint d p pat@(CPCon i as) =
     let notTpl = getIdString i /= ","
         bs = if notTpl then as else pUnmkTuple pat
     in pparen (notTpl && p>(maxPrec-1)) $
       (if notTpl then t"tagged" <+> pvpId d i else empty )<+> t "{" <>
                (catList(map (pvPrint d maxPrec) bs) (t","))<>t"}"

    pvPrint d p (CPstruct _ tyc []) | tyc == idPrimUnit = text "()"
    pvPrint d p (CPstruct _ tyc [(_, fst), (_, snd)]) | tyc == idPrimPair =
        pparen True (pvPrint d 0 fst <> t"," <+> pvPrint d 0 snd)
    pvPrint d p (CPstruct _ i fs) = pparen (p>(maxPrec-1)) $ pvpId d i <+> t "{" <+> sep (map ppFld fs ++ [t"}"])
        where ppFld (i, CPVar i') | i == i' = pvpId d i <> t";"
              ppFld (i, p) = pvpId d i <+> t "=" <+> pp d p <> t";"
    pvPrint d p (CPAs a pp) = pvPrint d maxPrec a <> t"@" <> pvPrint d maxPrec pp
    pvPrint d p (CPAny _) = text ".*"
    pvPrint d p (CPLit l) = pvPrint d p l
    pvPrint d p (CPMixedLit _ base ps) =
        let digitBits = log2 base
            f (len, Just val) = integerFormat (len `div` digitBits) base val
            f (len, Nothing)  = genericReplicate (len `div` digitBits) '?'
            pref  2 = "'b"
            pref  8 = "'o"
            pref 10 = "'d"
            pref 16 = "'h"
            pref x = internalError ("bad radix to CPMixedLit: " ++ show x)
        in  text (pref base ++ concatMap f ps)
    pvPrint d p (CPOper ops) = pparen (p > maxPrec-1) (sep (map (pvPrint d (maxPrec-1)) ops))
    pvPrint d p (CPCon1 _ i a) = pvPrint d p (CPCon i [a])
    ----
    pvPrint d p (CPConTs _ i ts as) = pparen (p>(maxPrec-1)) $ sep (pvpId d i : map ppApArg ts ++ map (pvPrint d maxPrec) as)
        where ppApArg ty = t"\183" <> pvPrint d maxPrec ty

instance PVPrint CPOp where
    pvPrint d _ (CPRand p) = pp d p
    pvPrint d _ (CPRator _ i) = ppInfix d i

-----

-- extra instances, where PPrint instance was outside CSyntax:

-- Ids
-- moved to Id.hs

-- Literals
-- moved to Literal.hs

-- Types

unravel :: Type -> (Type,[Type])
unravel (TAp (TAp a b) c) =
  let (x, ys) = unravel (TAp a b)
  in (x, ys ++[c])
unravel (TAp a b) = (a, [b])
unravel x = internalError ("unravel bad: " ++ show x)

tUnmkTuple :: Type -> [Type]
tUnmkTuple (TAp (TAp (TCon pair) a) b) | isTConPair pair =
  let bs = tUnmkTuple b
  in a:bs
tUnmkTuple x = [x]

instance PVPrint Type where
    pvPrint d p (TCon (TyCon special _ _))
        | special == idPrimUnit = text "void"
        -- These are needed when printing a function/method,
        -- because Action/ActionValue are keywords which introduce implicit
        -- action..endaction or actionvalue..endactionvalue blocks.
        -- It used to be that displaying "Prelude::Action" would print
        -- broken code, because then it's no longer using the keyword.
        -- So this code is to ensure that those places print the keyword,
        -- but it affects all other printing of the type, too.
        | special == idAction = text "Action"
        | special == idActionValue = text "ActionValue"
    pvPrint d p (TCon c) = pvPrint d 0 c
    pvPrint d p (TVar i) = pvPrint d 0 i
    pvPrint d p ty@(TAp (TCon (TyCon av _ _)) (TCon (TyCon special _ _)))
        -- ActionValue#(void) ==> Action
        | (qualEq idActionValue av) && (qualEq special idPrimUnit)
            = text "Action"
    pvPrint d p ty@(TAp (TAp (TCon special) a) b)
        | isTConPair special =
            let ts = tUnmkTuple ty
                n  = length ts
            in  t"Tuple" <> t(show n) <> pvParameterTypes d ts
        | isTConArrow special =
            pparen (p > 8) (ppTypedId d Nothing (t"f") ty newIds)
--        pparen (p > 8) (sep [pvPrint d 9 a <+> text "->", pvPrint d 8 r])
    pvPrint d p (TAp e e') = pparen (p>9) $
        let (x, ys) = unravel (TAp e e')
        in pvPrint d 9 x <> t"#(" <> sepList (map (pvPrint d 0) ys) (text ",") <> t")"
    pvPrint d p (TGen _ n) = text ('_':show n)
    pvPrint d p (TDefMonad _) = text "default_module_type"

instance PVPrint TyVar where
    pvPrint d _ (TyVar i _ _) = pvpId d i

instance PVPrint TyCon where
    pvPrint d _ (TyCon i _ _) = pvpId d i
    pvPrint d _ (TyNum i _) = text (itos i)
    pvPrint d _ (TyStr s _) = text (show s)

-- CQTypes and CPreds

instance PVPrint CQType where
    pvPrint d p (CQType [] ct) = pvPrint d p ct
    pvPrint d p (CQType preds ct) = sep [text "(" <> sepList (map (pvPrint d 0) preds) (text ",") <> text ") =>", pvPrint d 0 ct]

instance PVPrint CPred where
    pvPrint d p (CPred (CTypeclass c) []) = pvpId d c
    pvPrint d p (CPred (CTypeclass c) ts) = pvpId d c <> text "#(" <> sepList (map (pvPrint d 0) ts) (text ",") <> text ")"

instance PVPrint Kind where
    pvPrint _ _ KStar = text "*"
    pvPrint _ _ KNum = text "#"
    pvPrint _ _ KStr = text "$"
    pvPrint d p (Kfun l r) = pparen (p>9) $ pvPrint d 10 l <+> text "->" <+> pvPrint d 9 r
    pvPrint _ _ (KVar i) = text (show i)

instance PVPrint PartialKind where
    pvPrint _ _ PKNoInfo = text "?"
    pvPrint _ _ PKStar = text "*"
    pvPrint _ _ PKNum = text "#"
    pvPrint _ _ PKStr = text "$"
    pvPrint d p (PKfun l r) = pparen (p>9) $ pvPrint d 10 l <+> text "->" <+> pvPrint d 9 r

instance PVPrint TISort where
    pvPrint d p (TItype n t) = pparen (p>0) $ text "TItype" <+> pvPrint d 0 n <+> pvPrint d 1 t
    pvPrint d p (TIdata is enum) = pparen (p>0) $ text (if enum then "TIdata (enum)" else "TIdata") <+> pvPrint d 1 is
    pvPrint d p (TIstruct ss is) = pparen (p>0) $ text "TIstruct" <+> pvPrint d 1 ss <+> pvPrint d 1 is
    pvPrint d p (TIabstract) = text "TIabstract"

instance PVPrint StructSubType where
    pvPrint _ _ ss = text (show ss)

instance PVPrint VName where
    pvPrint _ _ (VName s) = text s

instance PVPrint VModInfo where
    pvPrint d p v = pPrint d p v

instance PVPrint VeriPortProp where
    pvPrint d p v = text (drop 2 (show v))

-- Pragmas
-- Moved to Pragma.hs

-- IntLits
-- Moved to IntLits

-----

ppInfix :: PDetail -> Id -> Doc
ppInfix d i =
    case getBSVIdString i of
    ":=" -> t "<="
    "/=" -> t "!="
    s@(c:_) | isIdChar c -> t"`" <> t s <> t"`"
    s -> t s


-----
