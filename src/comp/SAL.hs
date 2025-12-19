{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module SAL(
    SContext,
    convAPackageToSAL
) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad(foldM)
import Control.Monad.State(State, runState, gets, get, put)
import Data.Maybe(mapMaybe)
import Data.Char(toLower)
import Data.List(intersperse, groupBy)

import Util(snd3, fst2of3, eqSnd, itos, concatMapM, map_deleteMany, makePairs)

import Error(internalError, ErrorHandle, bsWarning)
import Flags
import Eval
import PPrint
import Id
import IntLit
import Prim(PrimOp(..))
import VModInfo(VArgInfo(..))
import ASyntax
import ASyntaxUtil
import LambdaCalcUtil

-- TODO:
-- * filter out unused defs (such as arguments to foreign funcs/tasks)
-- * figure out how to handle gated clocks

-- -------------------------

-- requires that task splicing has already happened
--
convAPackageToSAL :: ErrorHandle -> Flags -> APackage -> IO SContext

-- avoid work if a dump wasn't requested
convAPackageToSAL errh flags apkg | not (hasDumpStrict flags DFdumpSAL) =
    let ctx_id = ctxId (apkg_name apkg)
    in  return (SContext ctx_id [] [])

-- handle noinline functions separately
convAPackageToSAL errh flags apkg0 | (apkg_is_wrapped apkg0) =
    let
        -- update the types of the primitives
        apkg = lcAPackageProcess errh flags apkg0

        ds    = apkg_local_defs apkg
        ifcs  = apkg_interface apkg
        defmap = M.fromList [ (i, d) | d@(ADef i _ _ _) <- ds ]

        -- there should be one value method, and its constant RDY
        fn_defs =
          case ifcs of
            [AIDef methId args _ p (ADef _ ret_t ret_e _) _ _,
             AIDef rdyId _ _ _ (ADef _ _ rdy_e _) _ _]
             | (isRdyId rdyId) && (isTrue rdy_e) ->
              -- this is very similar to convAIFace for AIDef,
              -- except that the function doesn't take a state argument
              -- and has a different name
              let
                  rt = convAType ret_t

                  argset = S.fromList (map fst args)
                  arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
                  arg_types = map snd arg_infos

                  -- get all the defs used by the return value
                  uses = getAExprDefs defmap M.empty [ret_e]

                  body = runCM defmap M.empty argset $ do
                           ret_expr <- convAExpr ret_e
                           ds <- mapM convUse (M.toList uses)
                           return $ sLet ds ret_expr
              in
                  [SDValue noinlineId (funcType arg_types rt) $
                     sLam arg_infos body]

            _ -> internalError ("convAPackageToSAL: noinline ifcs: " ++
                                ppReadable ifcs)

        -- context Id
        ctx_id = ctxId (apkg_name apkg)

        -- context comments
        cs = []
    in
        return $
        SContext ctx_id cs fn_defs

convAPackageToSAL errh flags apkg0 =
  case (chkAPackage "SAL" apkg0) of
   Just wmsgs -> do bsWarning errh wmsgs
                    let ctx_id = ctxId (apkg_name apkg0)
                    return (SContext ctx_id [] [])
   Nothing ->
    let
        -- update the types of the primitives etc
        apkg = lcAPackageProcess errh flags apkg0

        modId = apkg_name apkg
        avis  = apkg_state_instances apkg
        ds    = apkg_local_defs apkg
        rs    = apkg_rules apkg
        ifcs  = apkg_interface apkg
        inps  = getAPackageInputs apkg
        defmap = M.fromList [ (i, d) | d@(ADef i _ _ _) <- ds ]
        instmap = M.fromList [ (inst, (vn, ps, mtmap))
                                 | avi <- avis,
                                   let inst = avi_vname avi,
                                   let (vn, ps) = getSubModType avi,
                                   let mtmap = getSubModAVMethReturnTypes avi]
        mmap = mkMethodOrderMap avis

        -- declare the module type (record of submods)
        state_defs = makeModTypeDecl inps avis

        -- define the ctor (call submod ctors with inst args)
        ctor_defs = makeModCtorDecl defmap inps avis

        -- define each rule as a fn
        rule_defs = map (convARule defmap instmap mmap) rs

        -- define each method as a fn
        ifc_defs = concatMap (convAIFace defmap instmap mmap) ifcs

        -- context Id
        ctx_id = ctxId modId

        -- context comments
        cs = []
    in
        return $
        SContext ctx_id cs
            (state_defs ++
             ctor_defs ++
             rule_defs ++
             ifc_defs)

-- -------------------------

-- This dump was created for use in the SRI Smten tool (previously SERI),
-- which is why the data types are prepended with "S".

data SContext = SContext SId SComment [SDefn]
    deriving (Eq, Show)

data SId = SId String
    deriving (Eq, Show)

data SQId = SQId (Maybe (SId, [SType], [SExpr])) SId
    deriving (Eq, Show)

type SComment = [String]

-- Top level definition
data SDefn = SDComment SComment [SDefn]
           | SDType SId SType
           -- SDScalarType
           -- SDDatatType
           | SDValue SId SType SExpr
           -- SDContext
           -- SDModule
           deriving (Eq, Show)

data SType = STVar SQId
           -- for us, arrays are always indexed by subtype starting at zero
           -- so the number here is the size
           | STArray Integer SType
           -- | STSub
           | STTuple [SType]
           | STFunc SType SType
           | STRecord [(SId, SType)]
           -- | STState
           deriving (Eq, Show)

data SExpr = SLam [(SId, SType)] SExpr
           | SLet [(SId, SType, SExpr)] SExpr
           | SVar SQId
           | SIntLit Integer
           | SRealLit Double
           | SApply SExpr SExpr
           | SApplyInfix SExpr SId SExpr
           -- for us, arrays are always indexed by subtype starting at zero
           -- so the number here is the size
           | SArray SId Integer SExpr
           | SArrayUpd SExpr SExpr SExpr
           | SArraySel SExpr SExpr
           | SStruct [(SId, SExpr)]
           | SStructUpd SExpr SId SExpr
           | SStructSel SExpr SId
           | STuple [SExpr]
           | STupleUpd SExpr Integer SExpr
           | STupleSel SExpr Integer
           | SIf SExpr SExpr SExpr
           deriving (Eq, Show)

-- -----

instance NFData SContext where
  rnf (SContext id cmt defns) = rnf3 id cmt defns

instance NFData SId where
  rnf (SId s) = rnf s

instance NFData SDefn where
  rnf (SDComment cmt defns) = rnf2 cmt defns
  rnf (SDType sid typ) = rnf2 sid typ
  rnf (SDValue sid typ expr) = rnf3 sid typ expr

instance NFData SQId where
  rnf (SQId mctx sid) = rnf2 mctx sid

instance NFData SType where
  rnf (STVar qid) = rnf qid
  rnf (STArray sz t) = rnf2 sz t
  rnf (STTuple ts) = rnf ts
  rnf (STFunc t1 t2) = rnf2 t1 t2
  rnf (STRecord fs) = rnf fs

instance NFData SExpr where
  rnf (SLam args body) = rnf2 args body
  rnf (SLet defs body) = rnf2 defs body
  rnf (SVar qid) = rnf qid
  rnf (SIntLit v) = rnf v
  rnf (SRealLit v) = rnf v
  rnf (SApply f e) = rnf2 f e
  rnf (SApplyInfix e1 op e2) = rnf3 e1 op e2
  rnf (SArray sid sz e) = rnf3 sid sz e
  rnf (SArrayUpd arr idx val) = rnf3 arr idx val
  rnf (SArraySel arr idx) = rnf2 arr idx
  rnf (SStruct fs) = rnf fs
  rnf (SStructUpd se sid se2) = rnf3 se sid se2
  rnf (SStructSel se sid) = rnf2 se sid
  rnf (STuple es) = rnf es
  rnf (STupleUpd te n te2) = rnf3 te n te2
  rnf (STupleSel te n) = rnf2 te n
  rnf (SIf c t f) = rnf3 c t f

-- -----

instance PPrint SContext where
  pPrint d p (SContext i cs ds) =
      ppComment cs $+$
      (pPrint d 0 i <+> colon <+> text "CONTEXT" <+> equals) $+$
      -- for readability, put an empty line at the start and end
      beginEnd (vsepEmptyLine ([empty] ++ map (pPrint d 0) ds ++ [empty]))

instance PPrint SId where
  pPrint d p (SId i) = text i

instance PPrint SQId where
  pPrint d p (SQId Nothing i) = pPrint d 0 i
  pPrint d p (SQId (Just (ctx, ts, es)) i) =
      let -- don't add spaces, so that it reads as a unit
          ts_doc = hcat $ intersperse comma $ map (pPrint d 0) ts
          es_doc = hcat $ intersperse comma $ map (pPrint d 0) es
          ps_doc = case (ts, es) of
                     ([], []) -> empty
                     ([], _)  -> lbrace <> es_doc <> rbrace
                     (_, [])  -> lbrace <> ts_doc <> rbrace
                     (_, _)   -> lbrace <> ts_doc <> semi <> es_doc <> rbrace
      in  pPrint d 0 ctx <> ps_doc <> text "!" <> pPrint d 0 i

instance PPrint SDefn where
  pPrint d p (SDComment cs ds) =
      ppComment cs $+$
      vsep (map (pPrint d 0) ds)
  pPrint d p (SDType i t) =
      sep [pPrint d 0 i <+> colon <+> text "TYPE" <+> equals,
           nest 2 (pPrint d 0 t <+> semi)]
  pPrint d p (SDValue i t e) = ppDef d (i, t, e) <+> semi

instance PPrint SType where
  pPrint d p (STVar i) = pPrint d 0 i
  pPrint d p (STArray sz t) =
      text "ARRAY" <+> ppArraySize sz <+> text "OF" <+> pPrint d 0 t
  pPrint d p (STTuple ts) =
      lbrack <+> commaSep (map (pPrint d 0) ts) <+> rbrack
  pPrint d p (STFunc t1 t2) =
      lbrack <+> pPrint d 0 t1 <+> text "->" <+> pPrint d 0 t2 <+> rbrack
  pPrint d p (STRecord fs) =
      let fdocs = map (ppField d) fs
      in  case fdocs of
            [] -> internalError ("STRecord with no fields")
            [d] -> lhbrack <+> d <+> rhbrack
            _ -> let spcomma = text " ,"
                     sprhbrack = text " #]"
                 in  vcat $
                       (zipWith (<+>) (lhbrack : repeat spcomma) fdocs) ++
                       [sprhbrack]

instance PPrint SExpr where
  pPrint d p (SLam as e) =
      (text "LAMBDA" <+> ppVarDecls d as <+> colon) $+$
      pPrint d 0 e
  pPrint d p e@(SLet ds body) =
      let mkDefDocs [] = internalError ("empty SLet")
          mkDefDocs [def] = [text "LET" <+> ppDef d def]
          mkDefDocs defs =
              zipWith (<+>) (text "LET" : repeat (nest 2 comma)) (map (ppDef d) defs)
          recFn (SLet ds body) =
              case (recFn body) of
                (doc:docs) -> (mkDefDocs ds) ++ ((text "IN" <+> doc):docs)
                _ -> internalError ("pPrint SLet")
          recFn body = [pPrint d 0 body]
       in vsep (recFn e)
  pPrint d p (SVar i) = pPrint d 0 i
  pPrint d p (SIntLit v) = pPrint d 0 v
  pPrint d p (SRealLit v) = pPrint d 0 v
  -- there is one unary operator
  -- rather than represent it with SApplyUnary, we treat is specially here
  pPrint d p (SApply f e) | (f == notVar) =
      pparen (p > 0) $ pPrint d 0 f <+> pPrint d 1 e
  -- print application to a tuple like a C-style function
  pPrint d p (SApply f (STuple es)) =
      pPrint d 1 f <>
      -- tuples are printed with space between the parentheses
      --pPrint d 0 a
      lparen <> commaSep (map (pPrint d 0) es) <> rparen
  -- print application to a single argument like a C-style function
  pPrint d p (SApply f a) =
      pPrint d 1 f <> pparen True (pPrint d 0 a)
{-
  pPrint d p (SApply f as) =
      pparen (p > 0) $
        -- allow the arguments to nest under the function
        sep ((pPrint d 1 f):(map (nest 4 . pPrint d 1) as))
-}
  pPrint d p (SApplyInfix a1 op a2) =
      pparen (p > 0) $
        pPrint d 1 a1 <+> pPrint d 0 op <+> pPrint d 1 a2
  pPrint d p (SArray i sz e) =
      sep [lbrack <>
             (lbrack <+> pPrint d 0 i <+> colon <+> ppArraySize sz <+> rbrack),
           nest 2 $ pPrint d 0 e <+> rbrack]
  pPrint d p (SArrayUpd arr_e idx_e val_e) =
      -- allow WITH to nest directly under the array expression,
      -- because we build arrays with many nested updates
      sep [pPrint d 0 arr_e,
           -- XXX if idx_e is big, we could nest val_e under it
           text "WITH" <+> lbrack <> pPrint d 0 idx_e <> rbrack <+>
               text ":=" <+> pPrint d 0 val_e]
  pPrint d p (SArraySel arr_e idx_e) =
      cat [pPrint d 1 arr_e,
           nest 2 $ lbrack <> pPrint d 0 idx_e <> rbrack]
  pPrint d p (SStruct fs) =
      let fdocs = map (ppFieldDef d) fs
      in  case fdocs of
            [] -> lhparen <+> rhparen
            [d] -> lhparen <+> d <+> rhparen
            _ -> let spcomma = text " ,"
                     sprhparen = text " #)"
                 in  vcat $
                       (zipWith (<+>) (lhparen : repeat spcomma) fdocs) ++
                       [sprhparen]
  pPrint d p (SStructUpd se fi fe) =
      pPrint d 1 se <+> text "WITH" <+>
      text "." <> pPrint d 0 fi <+> text ":=" <+> pPrint d 0 fe
  pPrint d p (SStructSel se fi) =
      pPrint d 1 se <> text "." <> pPrint d 0 fi
  pPrint d p (STuple es) =
      lparen <+> commaSep (map (pPrint d 0) es) <+> rparen
  pPrint d p (STupleUpd te fn fe) =
      pPrint d 1 te <+> text "WITH" <+>
      text "." <> pPrint d 0 fn <+> text ":=" <+> pPrint d 0 fe
  pPrint d p (STupleSel te fn) =
      pPrint d 1 te <> text "." <> pPrint d 0 fn
  pPrint d p (SIf c t f) =
      pparen (p > 0) $
        sep [text "IF" <+> pPrint d 1 c,
             nest 2 $ text "THEN" <+> pPrint d 0 t,
             nest 2 $ text "ELSE" <+> pPrint d 0 f,
             text "ENDIF"]


-- return "empty" if there is no comment, which is the unit of $+$,
-- so there is no extra line in the output when there are no comments
ppComment :: [String] -> Doc
ppComment cs =
    let ppline str = text ("% " ++ str)
    in  foldr ($+$) empty (map ppline cs)

ppDef :: PDetail -> (SId, SType, SExpr) -> Doc
ppDef d (i, t, e) =
    let (as_doc, t', body) =
            case (e, t) of
              (SLam as body, STFunc _ rt) -> (ppVarDecls d as, rt, body)
              _ -> (empty, t, e)
    in  -- XXX do we want to allow putting the type on a new line?
        sep [(pPrint d 0 i <+> as_doc <+> colon <+> pPrint d 0 t' <+> text "="),
             nest 2 (pPrint d 0 body)]

ppField :: PDetail -> (SId, SType) -> Doc
ppField d (i, t) = pPrint d 0 i <+> colon <+> pPrint d 0 t

ppFieldDef :: PDetail -> (SId, SExpr) -> Doc
ppFieldDef d (i, e) = pPrint d 0 i <+> text ":=" <+> pPrint d 0 e

ppVarDecls :: PDetail -> [(SId, SType)] -> Doc
ppVarDecls d [] = internalError ("SAL.ppVarDecls empty")
ppVarDecls d as =
    let as' = let getInfo its@((_,t):_) = (map fst its, t)
                  getInfo _ = internalError "SAL.ppVarDecls getInfo"
              in  map getInfo (groupBy eqSnd as)
        ppArg (is, t) =
            commaSep (map (pPrint d 0) is) <+> colon <+> pPrint d 0 t
    in  lparen <> commaSep (map ppArg as') <> rparen

ppArraySize :: Integer -> Doc
ppArraySize sz = lbrack <> text ("0.." ++ itos (sz-1)) <> rbrack

lhbrack, rhbrack :: Doc
lhbrack = text "[#"
rhbrack = text "#]"

lhparen, rhparen :: Doc
lhparen = text "(#"
rhparen = text "#)"

vsepEmptyLine :: [Doc] -> Doc
vsepEmptyLine [] = empty
vsepEmptyLine xs = foldr1 (\x y -> x $+$ text "" $+$ y) xs

beginEnd :: Doc -> Doc
beginEnd body =
    text "BEGIN" $+$
    nest 2 body $+$
    text "END"

-- -----

{-
usesSVar :: SQId -> SExpr -> Bool
usesSVar qi (SLam vars body) =
    case qi of
      SQId Nothing i | isJust (lookup i vars) -> False
      _ -> usesSVar qi body
usesSVar qi (SLet bs body) =
    case qi of
      SQId Nothing i | (i `elem` (map fst3 bs)) -> False
      _ -> any (usesSVar qi) (body : map thd bs)
usesSVar qi (SVar v) = (v == qi)
usesSVar qi (SIntLit _) = False
usesSVar qi (SRealLit _) = False
usesSVar qi (SApply f a) = any (usesSVar qi) [f, a]
usesSVar qi (SApplyInfix e1 _ e2) = any (usesSVar qi) [e1, e2]
usesSVar qi (SStruct fs) = any (usesSVar qi) (map snd fs)
usesSVar qi (SStructUpd se _ fe) = any (usesSVar qi) [se, fe]
usesSVar qi (SStructSel se _) = usesSVar qi se
usesSVar qi (STuple es) = any (usesSVar qi) es
usesSVar qi (STupleUpd te _ e) = any (usesSVar qi) [te, e]
usesSVar qi (STupleSel te _) = usesSVar qi te
usesSVar qi (SIf c te fe) = any (usesSVar qi) [c, te, fe]
-}

-- -------------------------

funcType :: [SType] -> SType -> SType
funcType [] rt = rt
funcType [t] rt = STFunc t rt
funcType ts rt = STFunc (STTuple ts) rt

-- -----

-- Primitives

-- no parameters
primCtx :: SId -> SQId
primCtx baseId = SQId (Just (SId "Prim", [], [])) baseId

-- one size parameter
prim1Ctx :: Integer -> SId -> SQId
prim1Ctx sz baseId = SQId (Just (SId "Prim1", [], [SIntLit sz])) baseId

-- two size parameters
prim2Ctx :: Integer -> Integer -> SId -> SQId
prim2Ctx sz1 sz2 baseId =
    let es = [SIntLit sz1, SIntLit sz2]
    in  SQId (Just (SId "Prim2", [], es)) baseId

-- an array and a size
arrPrim1Ctx :: Integer -> SType -> Integer -> SId -> SQId
arrPrim1Ctx arrsz elemty sz baseId =
    let es = [SIntLit arrsz, SIntLit sz]
    in  SQId (Just (SId "ArrayPrim1", [elemty], es)) baseId

bitToBoolVar :: SExpr
bitToBoolVar = SVar $ primCtx (SId "bitToBool")

boolToBitVar :: SExpr
boolToBitVar = SVar $ primCtx (SId "boolToBit")

-- -----

anyVar :: AType -> SExpr
anyVar (ATBit width)       = SVar $ bitCtx width (SId "undef")
anyVar t | (t == mkATBool) = SVar $ primCtx (SId "undefBool")
anyVar (ATString _)        = SVar $ stringCtx (SId "undef")
anyVar (ATReal)            = SVar $ primCtx (SId "undefReal")
anyVar (ATArray sz t)      = arrBuild sz $
                               replicate (fromInteger sz) (anyVar t)
anyVar t@(ATAbstract {})   = internalError ("anyVar: " ++ ppReadable t)

-- -----

boolType :: SType
boolType = sTVar (SId "BOOLEAN")

falseCon :: SExpr
falseCon = sVar (SId "FALSE")

trueCon :: SExpr
trueCon = sVar (SId "TRUE")

-- -----

voidCtx :: SId -> SQId
voidCtx baseId = SQId (Just (SId "Unit", [], [])) baseId

voidType :: SType
voidType = STVar (voidCtx (SId "T"))

voidCon :: SExpr
voidCon = SVar (voidCtx (SId "unit"))

-- -----

bitCtx :: Integer -> SId -> SQId
bitCtx sz baseId = SQId (Just (SId "Bit", [], [SIntLit sz])) baseId

bitNType :: Integer -> SType
bitNType n = STVar (bitCtx n (SId "T"))

{-
bitUndet :: Integer -> SExpr
bitUndet sz = SVar $ bitCtx sz (SId "mkUndet")
-}

bitConst :: Integer -> Integer -> SExpr
bitConst sz n = SApply (SVar (bitCtx sz (SId "mkConst"))) (SIntLit n)

-- -----

realType :: SType
realType = sTVar (SId "REAL")

-- -----

-- Instead of removing Strings from the design, use a dummy value
-- (defined in String context)

stringCtx :: SId -> SQId
stringCtx baseId = SQId (Just (SId "String", [], [])) baseId

stringType :: SType
stringType = STVar (stringCtx (SId "T"))

stringLit :: String -> SExpr
stringLit _ = SVar (stringCtx (SId "mkConst"))

-- -----

arrType :: Integer -> SType -> SType
arrType sz elem_ty = STArray sz elem_ty

-- the Integer should be the same as the length of the list
arrBuild :: Integer -> [SExpr] -> SExpr
arrBuild sz [] = internalError ("arrBuild: empty array")
arrBuild sz (e0:es) =
    -- construct an array using array updates
    let z = SArray (SId "i") sz e0
        foldFn arr (n, e) = SArrayUpd arr (SIntLit n) e
    in  foldl foldFn z (zip [1..] es)

arrSelect :: Integer -> SType -> Integer -> SExpr -> SExpr -> SExpr
arrSelect arrsz elemty idxsz arr_e idx_e =
    -- the index will be a bit vector, so we can't use SArraySel
    let fnvar = SVar (arrPrim1Ctx arrsz elemty idxsz (SId "arrSelect"))
    in  sApply fnvar [arr_e, idx_e]

-- -----

tupleType :: [SType] -> SType
tupleType ts = STTuple ts

-- -------------------------

sLam :: [(SId, SType)] -> SExpr -> SExpr
sLam [] body = body
--sLam ((i,t):its) body = SLam i t (sLam its body)
sLam vars body = SLam vars body


sLet :: [(SId, SType, SExpr)] -> SExpr -> SExpr
sLet [] body = body
sLet [(i,t,e)] (SVar (SQId Nothing i2)) | (i == i2) = e
-- It is safe to put every def in its own SLet:
sLet (d:ds) body = SLet [d] (sLet ds body)
{-
-- We could try to do better, however this causes the "state" defs
-- to be separate from the "act" defs sometimes, so this needs some
-- exploration:
-- XXX We already have the dependency info when we tsort;
-- XXX is it more efficient to reuse that?
sLet ds body =
    let foldFn d@(di, _, _) (SLet ds2 body) =
            let (ds2_stay, ds2_lift) =
                    let uses_d (_, _, e) = usesSVar (SQId Nothing di) e
                    in  partition uses_d ds2
            in SLet ([d] ++ ds2_lift)
                   -- XXX is it too redundant to do this:
                   --(sLet ds2_stay body)
                   if (null ds2_stay) then body else (SLet ds2_stay body)
        -- if the original body isn't an SLet, then construct the first SLet
        foldFn d e = SLet [d] e
    in  foldr foldFn body ds
-}

-- This assumes that the application is via a tuple
sApply :: SExpr -> [SExpr] -> SExpr
sApply f [] = f
--sApply (SApply f as1) as2 = sApply f (as1 ++ as2)
sApply f as = SApply f (STuple as)


sVar :: SId -> SExpr
sVar i = SVar (SQId Nothing i)

sTVar :: SId -> SType
sTVar i = STVar (SQId Nothing i)


sIf :: SExpr -> SExpr -> SExpr -> SExpr
sIf pe te fe | (pe == trueCon) = te
sIf pe te fe | (pe == falseCon) = fe
sIf pe te fe = SIf pe te fe


andInfix :: SId
andInfix = SId "AND"

orInfix :: SId
orInfix = SId "||"

notVar :: SExpr
notVar = sVar (SId "NOT")


sBAnds :: [SExpr] -> SExpr
sBAnds [] = trueCon
sBAnds [b] = b
sBAnds (b:bs) = SApplyInfix b andInfix (sBAnds bs)

sBOrs :: [SExpr] -> SExpr
sBOrs [] = falseCon
sBOrs [b] = b
sBOrs (b:bs) = SApplyInfix b orInfix (sBOrs bs)

sBNot :: SExpr -> SExpr
sBNot b = SApply notVar b


-- construct the name for all other primitives
primId :: PrimOp -> SId
primId p = case (show p) of
             (c:cs) -> SId ((toLower c):cs)
             _ -> internalError ("primId: null op name")

-- -------------------------

-- To guarantee that constructors and variables are properly capitalized
-- and to avoid name-clash, we prefix all identifiers.

-- -----
-- Context name: CTX_<modname>

ctxId :: Id -> SId
ctxId i = SId ("CTX_" ++ getIdBaseString i)

qualSId :: Id -> [Integer] -> SId -> SQId
qualSId modId ns baseId =
    let ps = map SIntLit ns
    in  SQId (Just (ctxId modId, [], ps)) baseId

-- -----
-- Noinline functions: CTX_<fname>!fn

noinlineId :: SId
noinlineId = SId "fn"

noinlineQId :: String -> SQId
noinlineQId func = qualSId (mk_homeless_id func) [] $ noinlineId

-- -----
-- Module state types: CTX_<modName>!MOD

modTypeId :: SId
modTypeId = SId "STATE"

modType :: SType
modType = sTVar modTypeId

submodType :: String -> [Integer] -> SType
submodType mod ns = STVar $ qualSId (mk_homeless_id mod) ns $ modTypeId

-- The constructor function: CTX_<modName>!ctor
modCtorId :: SId
modCtorId = SId "ctor"

submodCtor :: String -> [Integer] -> SExpr
submodCtor mod ns = SVar $ qualSId (mk_homeless_id mod) ns $ modCtorId

-- Lambda-binding for instantiation values passed to the constructor
-- (for setting the port/param values in the state): val_<name>
modArgId :: Id -> SId
modArgId argId = SId ("val_" ++ getIdBaseString argId)

-- -----
-- Fields of the state struct:
--   inst_<instname>
--   port_<portname>
--   param_<paramname>

-- Fields of datatypes in Haskell (and thus LC) must be unique,
-- so these functions add the <mod> as a further uniquifier.

instFieldId :: Id -> SId
instFieldId instId = SId ("inst_" ++ getIdBaseString instId)

portFieldId :: Id -> SId
portFieldId portId = SId ("port_" ++ getIdBaseString portId)

paramFieldId :: Id -> SId
paramFieldId paramId = SId ("param_" ++ getIdBaseString paramId)

-- -----
-- Rule function names: rule_<rulename>

ruleId :: Id -> SId
ruleId rId = SId ("rule_" ++ getIdBaseString rId)

-- Rule type :: <state> -> (Bool, <state>)
ruleType :: SType -> SType
ruleType stateType =
    funcType [stateType] (tupleType [boolType, stateType])

-- -----
-- Method function names: meth_<methname>

modMethId :: Id -> SId
modMethId methId = SId ("meth_" ++ getIdBaseString methId)

submodMethVar :: String -> [Integer] -> Id -> SExpr
submodMethVar mod ns methId =
    SVar $ qualSId (mk_homeless_id mod) ns $ modMethId methId

-- Action method type :: {<arg> ->} <state> -> (<state>, <rettype>)
actionMethType :: [SType] -> SType -> SType -> SType
actionMethType argTypes stateType returnType =
    funcType (argTypes ++ [stateType])
             (tupleType [stateType, returnType])

-- Value method type :: {<arg> ->} <state> -> <rettype>
valueMethType :: [SType] -> SType -> SType -> SType
valueMethType argTypes stateType returnType =
    funcType (argTypes ++ [stateType]) returnType

-- Lambda-binding for method arguments: arg_<name>
methArgId :: Id -> SId
methArgId argId = SId ("arg_" ++ getIdBaseString argId)

-- -----
-- let-bound defs: def_<name>

defId :: Id -> SId
defId def = SId ("def_" ++ getIdBaseString def)

defVar :: Id -> SExpr
defVar def = sVar (defId def)

-- -------------------------

-- lambda-bound variable name for the state
stateId :: SId
stateId = SId "state0"

-- reference to the lambda-bound state
stateVar :: SExpr
stateVar = sVar stateId

-- -------------------------

makeModTypeDecl :: [(AAbstractInput, VArgInfo)] -> [AVInst] -> [SDefn]
makeModTypeDecl inps avis =
    let
        -- ports/params are Bit type
        mkInputField (AAI_Port (i, t), Port {}) =
            Just $ (portFieldId i, convAType t)
        mkInputField (AAI_Port (i, t), Param {}) =
            Just $ (paramFieldId i, convAType t)
        mkInputField _ = Nothing

        inp_fs = mapMaybe mkInputField inps

        mkSubmodField avi =
            let fname = instFieldId (avi_vname avi)
                (submod, submod_tys) = getSubModType avi
            in  (fname, submodType submod submod_tys)

        inst_fs = map mkSubmodField avis

        -- SAL does not support records with no fields
        fs = inp_fs ++ inst_fs
        mod_ty = if (null fs)
                 then voidType
                 else STRecord fs
    in
        [SDType modTypeId mod_ty]

-- -------------------------

makeModCtorDecl :: DefMap -> [(AAbstractInput, VArgInfo)] -> [AVInst] ->
                   [SDefn]
makeModCtorDecl defmap inps avis =
    let
        -- ports/params are Bit type
        getInputInfo (AAI_Port (i, t), Port {}) =
            Just (modArgId i, convAType t, portFieldId i)
        getInputInfo (AAI_Port (i, t), Param {}) =
            Just (modArgId i, convAType t, paramFieldId i)
        getInputInfo _ = Nothing

        inp_infos = mapMaybe getInputInfo inps
        inp_types = map snd3 inp_infos
        ctor_args = map fst2of3 inp_infos

        ctor_type = funcType inp_types modType

        mkInputField (a, _, f) = (f, sVar a)

        inp_fs = map mkInputField inp_infos

        mkInstField :: ([(SId, SExpr)], M.Map AId (AType, AExpr)) ->
                       AVInst -> CM ([(SId, SExpr)], M.Map AId (AType, AExpr))
        mkInstField (accum_fs, accum_uses) avi = do
            let fname = instFieldId (avi_vname avi)
                (submod, submod_tys, args) = getSubModArgs avi
                submod_ctor = submodCtor submod submod_tys
            inst_args <- mapM convAExpr args
            let f = (fname, sApply submod_ctor inst_args)
                accum_fs' = (f:accum_fs)
                accum_uses' = getAExprDefs defmap accum_uses args
            return (accum_fs', accum_uses')

        (inst_fs, letdefs) =
            runCM defmap M.empty S.empty $ do
              (fs, uses) <- foldM mkInstField ([], M.empty) (reverse avis)
              ds <- mapM convUse (M.toList uses)
              return (fs, ds)

        -- SAL does not support records with no fields
        fs = inp_fs ++ inst_fs
        ctor_body = if (null fs)
                    then voidCon
                    else sLam ctor_args $
                           sLet letdefs $
                             SStruct fs
    in
        [SDValue modCtorId ctor_type ctor_body]

-- -------------------------

convARule :: DefMap -> InstMap -> MethodOrderMap -> ARule -> SDefn
convARule defmap instmap mmap r@(ARule rId _ _ _ p as _ _) =
  let
      body = runCM defmap instmap S.empty $ convRuleActions mmap p as
  in
      SDValue (ruleId rId) (ruleType modType) $
        sLam [(stateId, modType)] $
          body

-- -------------------------

convAIFace :: DefMap -> InstMap -> MethodOrderMap -> AIFace -> [SDefn]

convAIFace defmap instmap mmap
           (AIDef methId args _ p (ADef _ ret_t ret_e _) _ _) =
  let
      rt = convAType ret_t

      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      -- get all the defs used by the return value
      uses = getAExprDefs defmap M.empty [ret_e]

      body = runCM defmap instmap argset $ do
                 ret_expr <- convAExpr ret_e
                 ds <- mapM convUse (M.toList uses)
                 return $ sLet ds ret_expr
  in
      [SDValue (modMethId methId) (valueMethType arg_types modType rt) $
         sLam (arg_infos ++ [(stateId, modType)]) $
           body]

convAIFace defmap instmap mmap
           (AIAction args _ p methId rs _) =
  let
      -- arguments are Bit type
      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      body = runCM defmap instmap argset $
               convAIFaceBody mmap methId rs Nothing
  in
      [SDValue (modMethId methId) (actionMethType arg_types modType voidType) $
         sLam (arg_infos ++ [(stateId, modType)]) $
           body]

convAIFace defmap instmap mmap
           (AIActionValue args _ p methId rs (ADef _ def_t def_e _) _) =
  let
      -- return value is Bit type
      ret_ty = convAType def_t

      -- arguments are Bit type
      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      body = runCM defmap instmap argset $
               convAIFaceBody mmap methId rs (Just def_e)
  in
      [SDValue (modMethId methId) (actionMethType arg_types modType ret_ty) $
         sLam (arg_infos ++ [(stateId, modType)]) $
           body]

-- ignore clocks, resets, inouts
-- XXX do we need to make clock gates available?
convAIFace _ _ _ _ = []


-- the common conversion for the body of Action and ActionValue methods
convAIFaceBody :: MethodOrderMap -> AId -> [ARule] -> Maybe AExpr ->
                  CM SExpr
convAIFaceBody mmap methId rs m_ret = do
  defmap <- gets defMap
  let
      -- get all the defs used in the predicates of the rules
      pred_uses = getAExprDefs defmap M.empty (map arule_pred rs)

      -- conv one rule
      convRule (ARule _ _ _ _ p as _ _) = do
        p_expr <- convAExpr p
        -- convert the body without a predicate
        -- (and assuming that the pred_uses are already in scope)
        r_upd <- convMethActions (M.keys pred_uses) mmap as m_ret
        return (p_expr, r_upd)

      -- fold this in reverse
      foldFn accum r = do
        (p_expr, r_upd) <- convRule r
        return $ sIf p_expr r_upd accum

  -- XXX When there are split rules, the return value is duplicated.
  -- XXX We can lift the return value out, and exclude its uses from
  -- XXX inside the converted bodies.
  case rs of
    [] -> internalError ("convAIFace: no rules: " ++ ppReadable methId)
    -- a special case for one rule might have to check whether the rule's
    -- predicate is True (can we have split rules where one rule is removed,
    -- leaving one rule with a non-True predicate?)
    rs -> do
      -- the predicates in the if-else structure may refer to defs
      ds <- mapM convUse (M.toList pred_uses)
      -- we don't assume that the predicates are complete,
      -- so the final branch is a null update
      null_upd <- convMethActions (M.keys pred_uses) mmap [] m_ret
      rs_expr <- foldM foldFn null_upd (reverse rs)
      return $ sLet ds rs_expr

-- -------------------------

data ConvState =
    ConvState {
        defMap :: DefMap,
        instMap :: InstMap,
        -- the arguments to a method, when converting in a method body
        argSet :: S.Set AId,

        -- store of unique numbers for generating let-binding names
        uniqueNum :: Integer,

        -- the current state
        curState :: SExpr
    }

type CM = State ConvState

runCM :: DefMap -> InstMap -> S.Set AId -> (CM a) -> a
runCM defmap instmap argset fn =
    let state0 = ConvState { defMap  = defmap,
                             instMap = instmap,
                             argSet  = argset,
                             uniqueNum = 1,
                             curState = stateVar }
    in  fst $ runState fn state0

getUniqueNum :: CM Integer
getUniqueNum = do
  s <- get
  let n = uniqueNum s
  put (s { uniqueNum = n + 1 })
  return n

setState :: SExpr -> CM ()
setState newState = do
  s <- get
  put (s { curState = newState })

setUniqueNum :: Integer -> CM ()
setUniqueNum n = do
  s <- get
  put (s { uniqueNum = n })

-- -------------------------

convAType :: AType -> SType
convAType (ATBit width) = bitNType width
convAType (ATString Nothing) = stringType
convAType (ATString (Just width)) = stringType -- XXX ?
convAType (ATReal) = realType
convAType (ATArray sz t) = arrType sz (convAType t)
convAType t | (t == mkATBool) = boolType
convAType t@(ATAbstract {}) = internalError ("convAType: " ++ ppReadable t)

-- -----

convRuleActions :: MethodOrderMap -> AExpr -> [AAction] -> CM SExpr
convRuleActions mmap p as = convActions True [] mmap p as Nothing

convMethActions :: [AId] -> MethodOrderMap -> [AAction] -> Maybe AExpr ->
                   CM SExpr
convMethActions ds mmap as m_ret = convActions False ds mmap mkATrue as m_ret

convActions :: Bool -> [AId] -> MethodOrderMap ->
               AExpr -> [AAction] -> Maybe AExpr ->
               CM SExpr
convActions isRule predefined_defs mmap p as m_ret = do
  defmap <- gets defMap

  -- get the current state/num, because we'll be changing them
  prev_state_expr <- gets curState
  prev_unique_num <- gets uniqueNum

  let
      -- get all defs used in the actions
      uses0 = getAActionDefs defmap M.empty as
      -- merge in the defs for the return value
      uses1 = case m_ret of
                Nothing -> uses0
                Just ret -> getAExprDefs defmap uses0 [ret]
      -- merge in the defs for the predicate
      uses2 = getAExprDefs defmap uses1 [p]
      -- remove the defs that already defined
      uses = map_deleteMany predefined_defs uses2

      -- order the defs and actions
      (ordered_stmts, avmap) =
          tsortActionsAndDefs mmap defmap uses as

  -- merge statements with common conditions into blocks
  let ordered_blocks = mergeStmts defmap ordered_stmts

  -- convert the pred first so that it uses the initial state
  p_expr <- convAExpr p

  let_defs <- concatMapM (convStmt avmap) ordered_blocks

  -- get the final state
  state_expr <- gets curState

  -- reset the state/num
  setState prev_state_expr
  setUniqueNum prev_unique_num

  -- OK to convert the return expression here, because any state
  -- references should have been lifted to their own defs
  ret_expr <- case m_ret of
                Nothing -> return voidCon
                Just ret -> convAExpr ret
  let ret_tup = if isRule
                then STuple [p_expr, state_expr]
                else STuple [state_expr, ret_expr]

  return $ sLet let_defs ret_tup


-- each statement generates let bindings, and possibly updates the state
-- used by the later statements
convStmt :: M.Map (AId, AId) (AId, AType) ->
            AStmt -> CM [(SId, SType, SExpr)]

convStmt _ (AStmtDef (ADef i t (AMethValue { }) _ )) =
  -- the action will assign the def, so skip it here
  return []

convStmt _ (AStmtDef (ADef i t (ATaskValue { }) _ )) =
  -- the action will assign the def, so skip it here
  return []

convStmt _ (AStmtDef (ADef i t e _)) = do
  e_expr <- convAExpr e
  return [(defId i, convAType t, e_expr)]

convStmt avmap (AStmtAction cset (ACall obj meth as)) = do
  let c = getCondExpr cset

  instmap <- gets instMap

  -- get the current state, because we'll be changing it
  prev_state <- gets curState

  -- convert the condition
  c_expr <- convAExpr c
  -- convert the arguments
  a_exprs <- mapM convAExpr as

  let
      -- the kind of module that this instance is
      (submod, submod_tys, meth_ty_map) = lookupMod instmap obj
      -- the function for the method call on this submodule type
      fnvar = submodMethVar submod submod_tys meth
      -- the field name for this instance in the state for the current module
      instname = instFieldId obj
      -- extract the state for this submod instance
      submod_state = SStructSel prev_state instname
      -- the type of the submod state
      submod_type = submodType submod submod_tys

      -- get the return type for the action
      -- and if it has a name, then return the def name to bind it to
      (av_type, maybe_av_id) =
          case (M.lookup (obj, meth) avmap) of
            Just (i, t) -> (convAType t, Just (defId i))
            Nothing -> -- no name because the value is unused
                       -- but we still need to declare the correct type
                       case (M.lookup (unQualId meth) meth_ty_map) of
                         Just t -> (convAType t, Nothing)
                         Nothing -> (voidType, Nothing)

  -- we'll create new defs "act#" and "state#" with a unique number
  n  <- getUniqueNum

  -- the method call
  let act_id = SId ("act" ++ itos n)
      act_expr = sApply fnvar (a_exprs ++ [submod_state])
      act_def = (act_id, tupleType [submod_type, av_type], act_expr)

  -- the resulting state
  let state_id = SId ("state" ++ itos n)
      -- don't apply the method if the condition is not True
      state_expr = sIf c_expr
                     (SStructUpd prev_state instname
                          (STupleSel (sVar act_id) 1))
                     prev_state
      state_def = (state_id, modType, state_expr)

  -- the return value
  let av_defs = case maybe_av_id of
                  Nothing -> []
                  Just av_id ->
                      let av_expr = STupleSel (sVar act_id) 2
                      in  [(av_id, av_type, av_expr)]

  -- reset the state
  setState (sVar state_id)

  return $ (act_def:state_def:av_defs)

convStmt _ (AStmtAction cset (AFCall i f isC as isAssumpCheck)) = do
  -- the effect is outside our scope, and there is no return value,
  -- so do nothing
  return []

convStmt _ (AStmtAction cset (ATaskAction i f isC k as tmp t b)) = do
  -- the effect is outside our scope, but there is a return value,
  -- so assign it to an unknown value
  case tmp of
    Just i -> let st = convAType t
              in return [(defId i, st, anyVar t)]
    Nothing ->
        -- its value is unused, so do nothing
        return []

convStmt avmap (AStmtIf cset tblk fblk) = do
  let c = getCondExpr cset

  -- get the current state, because we'll be changing it
  prev_state <- gets curState

  -- convert the condition
  c_expr <- convAExpr c

  -- convert the True branch
  tblk_defs <- concatMapM (convStmt avmap) tblk
  -- record the final state for this branch
  true_state <- gets curState

  -- convert the False branch, with the original state
  setState prev_state
  fblk_defs <- concatMapM (convStmt avmap) fblk
  -- record the final state for this branch
  false_state <- gets curState

  -- create new def "state#" for the chosen branch
  n <- getUniqueNum

  -- the resulting state
  let state_id = SId ("state" ++ itos n)
      state_expr = sIf c_expr true_state false_state
      state_def = (state_id, modType, state_expr)

  -- set the state
  setState (sVar state_id)

  return $ tblk_defs ++ fblk_defs ++ [state_def]

-- -----

convAExpr :: AExpr -> CM SExpr
convAExpr (ASInt _ t (IntLit _ _ v)) | (t == mkATBool) =
  case v of
    0 -> return falseCon
    1 -> return trueCon
    _ -> internalError ("convAExpr: invalid Bool: " ++ ppReadable v)
convAExpr (ASInt _ (ATBit width) (IntLit _ _ v)) =
  return $ bitConst width v
convAExpr e@(ASInt {}) =
  internalError ("convAExpr: non-bit ASInt: " ++ ppReadable e)

convAExpr e@(ASStr i t v) =
  return $ stringLit v

convAExpr e@(ASReal i t v) =
  return $ SRealLit v

convAExpr (ASDef t i) = return $ defVar i

convAExpr (ASPort t i) = do
  argset <- gets argSet
  if (S.member i argset)
    then -- just reference the argument
         return $ sVar $ methArgId i
    else -- select the value from the state
         -- XXX since this is read-only, we can take it from the original state
         -- XXX not from the sequenced state?
         return $ SStructSel stateVar (portFieldId i)
convAExpr (ASParam t i) = do
  -- select the value from the state
  -- XXX since this is read-only, we can take it from the original state
  -- XXX not from the sequenced state?
  return $ SStructSel stateVar (paramFieldId i)

-- if we know what value will be picked, use that
convAExpr (ASAny _ (Just e)) = convAExpr e
-- otherwise, use a primitive to express that it's an unknown
convAExpr (ASAny t Nothing) = return $ anyVar t

convAExpr (APrim _ t p args) = convAPrim p t args

convAExpr (AMethCall _ obj meth as) = do
  state_expr <- gets curState
  instmap <- gets instMap
  let (submod, submod_tys, _) = lookupMod instmap obj
      fnvar = submodMethVar submod submod_tys meth
      modState = SStructSel state_expr (instFieldId obj)
  a_exprs <- mapM convAExpr as
  return $ sApply fnvar (a_exprs ++ [modState])

convAExpr e@(AMethValue t obj meth) =
  -- these are handled by convStmts and are not expected here
  internalError("convAExpr: AMethValue: " ++ ppReadable e)

convAExpr (ANoInlineFunCall t _ (ANoInlineFun name _ _ _) as) = do
  let func_id = noinlineQId name
  a_exprs <- mapM convAExpr as
  return $ sApply (SVar func_id) a_exprs

convAExpr (AFunCall t i f isC as) =
  -- probably can't assume anything about two calls with the same arguments,
  -- XXX so don't do anything with "as" here?
  return $ anyVar t

convAExpr e@(ATaskValue t i f isC k) =
  -- these are handled by convStmts and are not expected here
  internalError("convAExpr: ATaskValue: " ++ ppReadable e)

-- These shouldn't appear
convAExpr (ASClock {}) = internalError "convAExpr: ASClock"
convAExpr (ASReset {}) = internalError "convAExpr: ASReset"
convAExpr (ASInout {}) = internalError "convAExpr: ASInout"

-- A gate might appear in a boolean condition
-- XXX but we don't yet know how to handle it, so have to assume any value
convAExpr (AMGate t o c) =
  return $ anyVar t

-- -----

convAPrim :: PrimOp -> AType -> [AExpr] -> CM SExpr

convAPrim PrimChr _ [a] = do
  a_expr <- convAExpr a
  return $ sApply bitToBoolVar [a_expr]

convAPrim PrimOrd _ [a] = do
  a_expr <- convAExpr a
  return $ sApply boolToBitVar [a_expr]

convAPrim PrimIf _ [c, t, f] = do
  c_expr <- convAExpr c
  t_expr <- convAExpr t
  f_expr <- convAExpr f
  return (SIf c_expr t_expr f_expr)

convAPrim PrimCase t (idx:dflt:ces) =
  -- XXX if this can be represented with a case-expr, do that
  let -- we didn't pass in an id, so make one up
      i = dummy_id
      foldFn (v, e) res =
          let c = APrim i aTBool PrimEQ [idx, v]
          in  APrim i t PrimIf [c, e, res]
  in  convAExpr (foldr foldFn dflt (makePairs ces))

convAPrim PrimArrayDynSelect t [arr, idx] = do
  arr_expr <- convAExpr arr
  idx_expr <- convAExpr idx
  let arrty = ae_type arr
      arrsz = getArraySize arrty
      elemty = getArrayElemType arrty
      idxsz = aSize idx
  return $ arrSelect arrsz (convAType elemty) idxsz arr_expr idx_expr

convAPrim PrimBuildArray arr_ty as = do
  a_exprs <- mapM convAExpr as
  -- XXX the size should also be the length of "as"
  let sz = getArraySize arr_ty
  return $ arrBuild sz a_exprs

-- removed in IExpand
-- convAPrim PrimArrayDynUpdate t as =

-- PrimBAnd and PrimBOr need to be converted to native infix operators
-- (in the ASyntax, they can handle variable arguments)
convAPrim PrimBAnd _ as = do
  a_exprs <- mapM convAExpr as
  return (sBAnds a_exprs)
convAPrim PrimBOr _ as = do
  a_exprs <- mapM convAExpr as
  return (sBOrs a_exprs)

-- represent "primBNot" with the native "NOT"
convAPrim PrimBNot _ [a] = do
  a_expr <- convAExpr a
  return (sBNot a_expr)

-- PrimConcat needs to be converted to a binary function
-- (in the ASyntax, it can handle variable arguments)
convAPrim p@(PrimConcat) t as@(_:_) = do
  let mapFn a = do a_expr <- convAExpr a
                   return (aSize a, a_expr)
  a_exprs <- mapM mapFn as
  let foldFn (sz1, a1) (sz2, a2) =
          (sz1 + sz2,
           sApply (SVar (prim2Ctx sz1 sz2 (primId p))) [a1, a2])
  return $ snd $ foldr1 foldFn a_exprs

convAPrim p@(PrimExtract) (ATBit sz2) [a, _, _] = do
  a_expr <- convAExpr a
  return $ sApply (SVar (prim2Ctx (aSize a) sz2 (primId p))) [a_expr]

-- converted to PrimSelect in IConv
--convAPrim PrimSplit t as =

-- only created in the Verilog backend
--convAPrim PrimMux t as =
--convAPrim PrimPriMux t as =

-- converted to PrimExtract in AConv
--convAPrim PrimSelect t as =

-- removed in AConv
--convAPrim PrimRange t as =

convAPrim p t as | p `elem` [ PrimAdd, PrimSub, PrimAnd, PrimOr, PrimXor,
                              PrimInv, PrimNeg ] = do
   a_exprs <- mapM convAExpr as
   return $ sApply (SVar (prim1Ctx (aSize t) (primId p))) a_exprs

-- treat equality of booleans different from equality of bit vectors
convAPrim p@(PrimEQ) t as@(a1:_) | (ae_type a1 == mkATBool) = do
   a_exprs <- mapM convAExpr as
   return $ sApply (SVar (primCtx (primId p))) a_exprs

-- equality and comparison of bit vectors
convAPrim p t as@(a1:_)
    | p `elem` [ PrimEQ, PrimULE, PrimULT, PrimSLE, PrimSLT ] = do
   a_exprs <- mapM convAExpr as
   return $ sApply (SVar (prim1Ctx (aSize a1) (primId p))) a_exprs

convAPrim p t as@[val, idx] | p `elem` [ PrimSL, PrimSRL, PrimSRA ] = do
   a_exprs <- mapM convAExpr as
   let sz1 = aSize val
       sz2 = aSize idx
   return $ sApply (SVar (prim2Ctx sz1 sz2 (primId p))) a_exprs

convAPrim p t as@[a1, a2] | p `elem` [ PrimMul, PrimQuot, PrimRem ] = do
   a_exprs <- mapM convAExpr as
   let sz1 = aSize a1
       sz2 = aSize a2
   return $ sApply (SVar (prim2Ctx sz1 sz2 (primId p))) a_exprs

convAPrim p t [a] | p `elem` [ PrimSignExt, PrimZeroExt, PrimTrunc ] = do
   a_expr <- convAExpr a
   let sz1 = aSize a
       sz2 = aSize t
   return $ sApply (SVar (prim2Ctx sz1 sz2 (primId p))) [a_expr]

convAPrim p _ as = do
  internalError ("convAPrim: " ++ ppReadable (p, as))

-- -----

-- convert the elements of a use map (returned by getAExprDefs etc)
convUse :: (AId, (AType, AExpr)) -> CM (SId, SType, SExpr)
convUse (i, (t, e)) = do
  e' <- convAExpr e
  return (defId i, convAType t, e')

-- -------------------------
