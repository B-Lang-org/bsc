{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module LambdaCalc(
    SPackage,
    convAPackageToLambdaCalc
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

import Util(snd3, fst2of3, itos, concatMapM, map_deleteMany, makePairs)

import Error(internalError, ErrorHandle, bsWarning)
import Flags
import Eval
import PPrint
import Id
import IntLit
import Prim(PrimOp(..))
import VModInfo(vName, VArgInfo(..), isParam, isPort, getVNameString)
import ASyntax
import LambdaCalcUtil

-- TODO:
-- * filter out unused defs (such as arguments to foreign funcs/tasks)
-- * figure out how to handle gated clocks

-- -------------------------

-- requires that task splicing has already happened
--
convAPackageToLambdaCalc :: ErrorHandle -> Flags -> APackage -> IO SPackage

-- avoid work if a dump wasn't requested
convAPackageToLambdaCalc errh flags apkg
  | not (hasDumpStrict flags DFdumpLambdaCalculus) = return (SPackage [] [])

-- handle noinline functions separately
convAPackageToLambdaCalc errh flags apkg0 | (apkg_is_wrapped apkg0) =
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

                  -- the module name is unused, but give one anyway;
                  -- use the method name (the apkg name has "module_" prepended)
                  body = runCM methId defmap M.empty argset $ do
                           ret_expr <- convAExpr ret_e
                           ds <- mapM convUse (M.toList uses)
                           return $ sLet ds ret_expr
              in
                  [SDValue (noinlineId methId) (funcType arg_types rt) $
                     sLam arg_infos body]

            _ -> internalError ("convAPackageToLambdaCalc: noinline ifcs: " ++
                                ppReadable ifcs)

        -- package comments
        cs = []
    in
        return $
        SPackage cs fn_defs

convAPackageToLambdaCalc errh flags apkg0 =
  case (chkAPackage "lambda-calculus" apkg0) of
   Just wmsgs -> do bsWarning errh wmsgs
                    return (SPackage [] [])
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
        state_defs = makeModStructDecl modId inps avis

        -- define the ctor (call submod ctors with inst args)
        ctor_defs = makeModCtor defmap modId inps avis

        -- define the dimension fn (call the dimension fn on submods)
        dim_defs = makeModDimDefn modId avis

        -- define each rule as a fn
        rule_defs = map (convARule defmap instmap mmap modId) rs

        -- define each method as a fn
        ifc_defs = concatMap (convAIFace defmap instmap mmap modId) ifcs

        -- package comments
        cs = []
    in
        return $
        SPackage cs (state_defs ++
                     ctor_defs ++
                     dim_defs ++
                     rule_defs ++
                     ifc_defs)

-- -------------------------

-- This dump was created for use in the SRI Smten tool (previously SERI),
-- which is why the data types are prepended with "S".

data SPackage = SPackage SComment [SDefn]
    deriving (Eq, Show)

type SComment = [String]

-- Top level definition
data SDefn = SDStruct Id [(Id, SType)]
           | SDValue Id SType SExpr
           | SDComment SComment [SDefn]
           deriving (Eq, Show)

data SType = STVar Id
           | STCon (STyCon)
           | STAp SType SType
           deriving (Eq, Show)

data STyCon = STyCon Id
            | STyNum Integer
            deriving (Eq, Show)

data SExpr = SLam Id SType SExpr
           | SLet [(Id, SType, SExpr)] SExpr
           | SVar Id
           | SCon Id
           | SBVLit Integer Integer  -- width, value
           | SStringLit String
           | SRealLit Double
           | SApply SExpr [SExpr]
           | SApplyInfix Id [SExpr]
           | SStruct Id [(Id, SExpr)]
           | SStructUpd SExpr [(Id, SExpr)]
           | SSelect SExpr Id
           | SIf SExpr SExpr SExpr
           | SHasType SType SExpr  -- type signature
           deriving (Eq, Show)

-- -----

instance NFData SPackage where
  rnf (SPackage cmt defns) = rnf2 cmt defns

instance NFData SDefn where
  rnf (SDStruct id flds) = rnf2 id flds
  rnf (SDValue id typ expr) = rnf3 id typ expr
  rnf (SDComment cmt defns) = rnf2 cmt defns

instance NFData STyCon where
  rnf (STyCon id) = rnf id
  rnf (STyNum n) = rnf n

instance NFData SType where
  rnf (STVar id) = rnf id
  rnf (STCon con) = rnf con
  rnf (STAp t1 t2) = rnf2 t1 t2

instance NFData SExpr where
  rnf (SLam id t e) = rnf3 id t e
  rnf (SLet defs body) = rnf2 defs body
  rnf (SVar id) = rnf id
  rnf (SCon id) = rnf id
  rnf (SBVLit w v) = rnf2 w v
  rnf (SStringLit s) = rnf s
  rnf (SRealLit v) = rnf v
  rnf (SApply f args) = rnf2 f args
  rnf (SApplyInfix op args) = rnf2 op args
  rnf (SStruct id fs) = rnf2 id fs
  rnf (SStructUpd e fs) = rnf2 e fs
  rnf (SSelect e id) = rnf2 e id
  rnf (SIf c t f) = rnf3 c t f
  rnf (SHasType t e) = rnf2 t e

-- -----

instance PPrint SPackage where
  pPrint d p (SPackage cs ds) =
      ppComment cs $+$
      vsepEmptyLine (map (pPrint d 0) ds)

instance PPrint SDefn where
  pPrint d p (SDComment cs ds) =
      ppComment cs $+$
      vsep (map (pPrint d 0) ds)
  pPrint d p (SDStruct i fs) =
      let fdocs = map (ppField d) fs
          fpunc =
            case fdocs of
              [] -> lbrace <+> rbrace
              [d] -> lbrace <+> d <+> rbrace
              _ -> vcat $
                     (zipWith (<+>) (lbrace : repeat comma) fdocs) ++ [rbrace]
      in  sep [text "data" <+> pPrint d 0 i <+> text "=",
               nest 4 (pPrint d 0 i),
               nest 8 (fpunc <> text ";")]
  pPrint d p (SDValue i t e) =
      pPrint d 0 i <+> text "::" <+> pPrint d 0 t <> text ";" $+$
      pPrint d 0 i <+> text "=" $+$
      nest 4 (pPrint d 0 e) <> text ";"

instance PPrint SType where
  pPrint d p c@(STCon _) | (c == voidType) = text "()"
  pPrint d p (STCon c) = pPrint d 0 c
  pPrint d p (STVar i) = pPrint d 0 i
  pPrint d p (STAp (STAp pair a) b) | (pair == pairTCon) =
      pparen (p >= 0) (hsep [pPrint d 0 a <> text ",", pPrint d (-1) b])
  pPrint d p (STAp (STAp arr a) r) | (arr == arrowTCon) =
      pparen (p > 8) (hsep [pPrint d 9 a <+> text "->", pPrint d 8 r])
  pPrint d p (STAp a b) =
      pparen (p > 9) (hsep [pPrint d 9 a, pPrint d 10 b])

instance PPrint STyCon where
  pPrint d p (STyCon i) = pPrint d 0 i
  pPrint d p (STyNum n) = text "#" <> pPrint d 0 n

instance PPrint SExpr where
  pPrint d p (SLam i t e) =
      pparen True $
        sep [text "\\" <+>
               pparen True (pPrint d 0 i <+> text "::" <+> pPrint d 0 t) <+>
               text "->",
             pPrint d 0 e]
  pPrint d p (SLet ds body) =
      let ppDef (i, t, e) =
            sep [pparen True (pPrint d 0 i <+> text "::" <+> pPrint d 0 t)
                     <+> text "=",
                 nest 4 (pPrint d 0 e)]
      in  pparen (p > 0)
            (
             (text "let" <+> encloseSep lbrace rbrace semi (map ppDef ds)) $$
             (text "in" <+> pPrint d 0 body)
            )
  pPrint d p (SVar i) | (getIdString i == "primChr") = text "bitToBool"
  pPrint d p (SVar i) | (getIdString i == "primOrd") = text "boolToBit"
  pPrint d p (SVar i) = pPrint d 0 i
  pPrint d p c@(SCon _) | (c == voidCon) = text "()"
  pPrint d p (SCon i) = pPrint d 0 i
  pPrint d p (SBVLit w v) =
      -- XXX if the value is large, consider displaying as hex
      pparen True (pPrint d 0 v <+> text "::" <+> pPrint d 0 (bitNType w))
  pPrint d p (SStringLit v) =
      doubleQuotes $ text v
  pPrint d p (SRealLit v) =
      pparen True (pPrint d 0 v <+> text "::" <+> pPrint d 0 realType)
  pPrint d p (SApply f as) =
      pparen (p > 0) $
        -- allow the arguments to nest under the function
        sep ((pPrint d 1 f):(map (nest 4 . pPrint d 1) as))
  -- special case for binary infix operators
  -- (commutative operators can take a variable number of arguments)
  pPrint _ _ (SApplyInfix _ as) | (length as < 2) =
      internalError ("SApplyInfix: " ++ ppReadable as)
  pPrint d p (SApplyInfix op as) =
      pparen (p > 0) $
        encloseSep empty empty (pPrint d 0 op) (map (pPrint d 1) as)
  pPrint d p (SStruct si fs) =
      let ppFieldDef (i, e) = sep [pPrint d 0 i <+> text "=",
                                   nest 4 (pPrint d 0 e)]
      in  pparen (p > 0) $
            sep ([pPrint d 0 si] ++
                 map (nest 4)
                     (enclose lbrace rbrace comma (map ppFieldDef fs)))
  pPrint d p (SStructUpd se fs) =
      let ppFieldDef (i, e) = sep [pPrint d 0 i <+> text "=",
                                   nest 4 (pPrint d 0 e)]
      in  pparen (p > 0) $
            sep ([pPrint d 0 se] ++
                 map (nest 4)
                     (enclose lbrace rbrace comma (map ppFieldDef fs)))
  pPrint d p (SSelect e f) =
      pPrint d p (SApply (SVar f) [e])
  pPrint d p (SIf c t f) =
      pparen (p > 0) $
        sep [text "if" <+> pPrint d 1 c,
             text "then" <+> pPrint d 0 t,
             text "else" <+> pPrint d 0 f]
  pPrint d p (SHasType t e) =
      pparen True (pPrint d 1 e <+> text "::" <+> pPrint d 0 t)


-- return "empty" if there is no comment, which is the unit of $+$,
-- so there is no extra line in the output when there are no comments
ppComment :: [String] -> Doc
ppComment cs =
    let ppline str = text ("-- " ++ str)
    in  foldr ($+$) empty (map ppline cs)

ppField :: PDetail -> (Id, SType) -> Doc
ppField d (i,t) = pPrint d 0 i <+> text "::" <+> pPrint d 0 t

vsepEmptyLine :: [Doc] -> Doc
vsepEmptyLine [] = empty
vsepEmptyLine xs = foldr1 (\x y -> x $+$ text "" $+$ y) xs

-- this is like "encloseSep" but without the call to "sep",
-- allowing it to be combined with other Doc in "sep" in the caller
enclose :: Doc -> Doc -> Doc -> [Doc] -> [Doc]
enclose left right punc ds =
    case ds of
      []  -> [left <+> right]
      [d] -> [left <+> d <+> right]
      _   -> let ps = zipWith (<+>) (left : repeat punc) ds
             in  ps ++ [right]


-- -------------------------

arrowTCon :: SType
arrowTCon = STCon (STyCon (mk_homeless_id "->"))

funcType :: [SType] -> SType -> SType
funcType [] rt = rt
funcType (t:ts) rt = STAp (STAp arrowTCon t) (funcType ts rt)

-- -----

-- a primitive indicating an unknown value with Type
anyTVar :: SType -> SExpr
anyTVar t = SHasType t (SVar (mk_homeless_id "primAny"))

-- -----

voidType :: SType
voidType = STCon (STyCon (mk_homeless_id "PrimUnit"))

voidCon :: SExpr
voidCon = SCon (mk_homeless_id "PrimUnit")

-- -----

boolType :: SType
boolType = STCon (STyCon (mk_homeless_id "Bool"))

falseCon :: SExpr
falseCon = SCon (mk_homeless_id "False")

trueCon :: SExpr
trueCon = SCon (mk_homeless_id "True")

-- -----

numType :: Integer -> SType
numType n = STCon (STyNum n)

bitTCon :: SType
bitTCon = STCon (STyCon (mk_homeless_id "Bit"))

bitNType :: Integer -> SType
bitNType n = STAp bitTCon (numType n)

-- -----

stringType :: SType
stringType = STCon (STyCon (mk_homeless_id "String"))

-- -----

realType :: SType
realType = STCon (STyCon (mk_homeless_id "Double"))

-- -----

arrTCon :: SType
arrTCon = STCon (STyCon (mk_homeless_id "Array"))

arrType :: Integer -> SType -> SType
arrType n t = STAp (STAp arrTCon (numType n)) t

-- -----

pairTCon :: SType
pairTCon = STCon (STyCon (mk_homeless_id "PrimPair"))

tupleType :: [SType] -> SType
tupleType [] = voidType
tupleType [t] = t
tupleType (t:ts) = STAp (STAp pairTCon t) (tupleType ts)

mktupleVar :: SExpr
mktupleVar = SVar (mk_homeless_id "mktuple")

fst3Var :: SExpr
fst3Var = SVar (mk_homeless_id "fst3")

snd3Var :: SExpr
snd3Var = SVar (mk_homeless_id "snd3")

thdVar :: SExpr
thdVar = SVar (mk_homeless_id "thd")

-- -------------------------

sLam :: [(Id, SType)] -> SExpr -> SExpr
sLam [] body = body
sLam ((i,t):its) body = SLam i t (sLam its body)


sLet :: [(Id, SType, SExpr)] -> SExpr -> SExpr
sLet [] body = body
sLet ds1 (SLet ds2 body) = sLet (ds1 ++ ds2) body
-- XXX does this lose a type annotation that's needed in some places?
sLet [(i,t,e)] (SVar i2) | (i == i2) = e
sLet ds body = SLet ds body


sApply :: SExpr -> [SExpr] -> SExpr
sApply f [] = f
sApply (SApply f as1) as2 = sApply f (as1 ++ as2)
sApply f as = SApply f as


sIf :: SExpr -> SExpr -> SExpr -> SExpr
sIf pe te fe | (pe == trueCon) = te
sIf pe te fe | (pe == falseCon) = fe
sIf pe te fe = SIf pe te fe


andInfix :: Id
andInfix = mk_homeless_id "&&"

orInfix :: Id
orInfix = mk_homeless_id "||"

notVar :: SExpr
notVar = SVar (mk_homeless_id "not")


-- note that we optimize for true values, but don't expect false
sBAnd :: SExpr -> SExpr -> SExpr
sBAnd b1 b2 | (b1 == trueCon) = b2
sBAnd b1 b2 | (b2 == trueCon) = b1
sBAnd b1 b2 = SApplyInfix andInfix [b1, b2]

sBAnds :: [SExpr] -> SExpr
sBAnds [] = trueCon
sBAnds [b] = b
sBAnds bs = SApplyInfix andInfix bs

sBOrs :: [SExpr] -> SExpr
sBOrs [] = falseCon
sBOrs [b] = b
sBOrs bs = SApplyInfix orInfix bs

sBNot :: SExpr -> SExpr
sBNot b = SApply notVar [b]


-- construct the name for all other primitives by dropping the "prim" prefix
-- and making it lowercase
primVar :: PrimOp -> SExpr
primVar p =
  let p_name = case (show p) of
                 (c:cs) -> ((toLower c):cs)
                 _ -> internalError ("primVar: null op name")
  in  SVar (mk_homeless_id p_name)

-- apply a binary primitive to 2 or more arguments
primBinAps :: SExpr -> [SExpr] -> SExpr
primBinAps p as@[] = internalError ("primBinAps: " ++ ppReadable (p, as))
primBinAps p as@[_] = internalError ("primBinAps: " ++ ppReadable (p, as))
primBinAps p [a1, a2] = SApply p [a1, a2]
primBinAps p (a:as) = SApply p [a, primBinAps p as]

-- -------------------------

-- To guarantee that constructors and variables are properly capitalized
-- and to avoid name-clash, we prefix all identifiers.

-- -----
-- Noinline functions: noinline_<funcname>

noinlineId :: Id -> Id
noinlineId funcId = mk_homeless_id ("noinline_" ++ getIdBaseString funcId)

-- -----
-- Module state types: MOD_<modname>

modTypeId :: Id -> Id
modTypeId modId = mk_homeless_id ("MOD_" ++ getIdBaseString modId)

modType :: Id -> [Integer] -> SType
modType modId ns =
    let con = STCon (STyCon (modTypeId modId))
        tys = map (STCon . STyNum) ns
    in  foldl STAp con tys

-- The constructor function: ctor_<modname>
modCtorId :: Id -> Id
modCtorId modId = mk_homeless_id ("ctor_" ++ getIdBaseString modId)

-- Lambda-binding for instantiation values passed to the constructor
-- (for setting the port/param values in the state): val_<name>
modArgId :: Id -> Id
modArgId argId = mk_homeless_id ("val_" ++ getIdBaseString argId)

-- Function to assert that a state value is consistent: dim_<modname>
modDimId :: Id -> Id
modDimId modId = mk_homeless_id ("dim_" ++ getIdBaseString modId)

-- -----
-- Fields of the state struct:
--   inst_<instname>__<mod>
--   port_<portname>__<mod>
--   param_<paramname>__<mod>
-- where <mod> is the module of which this is a submod/port/param

-- Fields of datatypes in Haskell (and thus LC) must be unique,
-- so these functions add the <mod> as a further uniquifier.

instFieldId :: Id -> Id -> Id
instFieldId modId instId =
    mk_homeless_id ("inst_" ++ getIdBaseString instId ++
                    "__" ++ getIdBaseString modId)

portFieldId :: Id -> Id -> Id
portFieldId modId portId =
    mk_homeless_id ("port_" ++ getIdBaseString portId ++
                    "__" ++ getIdBaseString modId)

paramFieldId :: Id -> Id -> Id
paramFieldId modId paramId =
    mk_homeless_id ("param_" ++ getIdBaseString paramId ++
                    "__" ++ getIdBaseString modId)

-- -----
-- Rule function names: rule_<rulename>_<modname>

ruleId :: Id -> Id -> Id
ruleId modId rId =
    mk_homeless_id ("rule_" ++ getIdBaseString rId ++
                    "_" ++ getIdBaseString modId)

-- Rule type :: <state> -> (Bool, <state>, ())
ruleType :: SType -> SType
ruleType stateType =
    funcType [stateType] (tupleType [boolType, stateType, voidType])

-- -----
-- Method function names: meth_<methname>_<modname>

methId :: String -> Id -> Id
methId mod meth =
    mk_homeless_id ("meth_" ++ getIdBaseString meth ++ "_" ++ mod)

-- Action method type :: {<arg> ->} <state> -> (Bool, <state>, <rettype>)
actionMethType :: [SType] -> SType -> SType -> SType
actionMethType argTypes stateType returnType =
    funcType (argTypes ++ [stateType])
             (tupleType [boolType, stateType, returnType])

-- Value method type :: {<arg> ->} <state> -> <rettype>
valueMethType :: [SType] -> SType -> SType -> SType
valueMethType argTypes stateType returnType =
    funcType (argTypes ++ [stateType]) returnType

-- Lambda-binding for method arguments: arg_<name>
methArgId :: Id -> Id
methArgId argId = mk_homeless_id ("arg_" ++ getIdBaseString argId)

-- -----
-- let-bound defs: def_<name>

defId :: Id -> Id
defId def = mk_homeless_id ("def_" ++ getIdBaseString def)

defVar :: Id -> SExpr
defVar def = SVar (defId def)

-- -------------------------

-- lambda-bound variable name for the state
stateId :: Id
stateId = mk_homeless_id "state0"

-- reference to the lambda-bound state
stateVar :: SExpr
stateVar = SVar stateId

-- a function that returns (False, ?, ?)
-- used as the default clause for split methods
nullUpdVar :: SExpr
nullUpdVar = SVar (mk_homeless_id "nullUpd")

-- -------------------------

makeModStructDecl :: Id -> [(AAbstractInput, VArgInfo)] -> [AVInst] -> [SDefn]
makeModStructDecl modId inps avis =
    let
        -- ports/params are Bit type
        mkInputField (AAI_Port (i, t), Port {}) =
            Just $ (portFieldId modId i, convAType t)
        mkInputField (AAI_Port (i, t), Param {}) =
            Just $ (paramFieldId modId i, convAType t)
        mkInputField _ = Nothing

        inp_fs = mapMaybe mkInputField inps

        mkSubmodField avi =
            let (mod, tys) = getSubModType avi
            in  (instFieldId modId (avi_vname avi),
                 modType (mk_homeless_id mod) tys)

        inst_fs = map mkSubmodField avis
    in
        [SDStruct (modTypeId modId) (inp_fs ++ inst_fs)]

-- -------------------------

makeModCtor :: DefMap -> Id -> [(AAbstractInput, VArgInfo)] -> [AVInst] ->
               [SDefn]
makeModCtor defmap modId inps avis =
    let
        mod_ty = modType modId []

        -- ports/params are Bit type
        getInputInfo (AAI_Port (i, t), Port {}) =
            Just (modArgId i, convAType t, portFieldId modId i)
        getInputInfo (AAI_Port (i, t), Param {}) =
            Just (modArgId i, convAType t, paramFieldId modId i)
        getInputInfo _ = Nothing

        inp_infos = mapMaybe getInputInfo inps
        inp_types = map snd3 inp_infos
        ctor_args = map fst2of3 inp_infos

        ctor_type = funcType inp_types mod_ty

        mkInputField (a, _, f) = (f, SVar a)

        inp_fs = map mkInputField inp_infos

        mkInstField :: ([(Id, SExpr)], M.Map AId (AType, AExpr)) ->
                       AVInst -> CM ([(Id, SExpr)], M.Map AId (AType, AExpr))
        mkInstField (accum_fs, accum_uses) avi = do
            let fname = instFieldId modId (avi_vname avi)
                submod = getVNameString (vName (avi_vmi avi))
                submod_ctor = SVar $ modCtorId (mk_homeless_id submod)
                args = [ e | (i, e) <- getInstArgs avi, isPort i || isParam i ]
            inst_args <- mapM convAExpr args
            let f = (fname, sApply submod_ctor inst_args)
                accum_fs' = (f:accum_fs)
                accum_uses' = getAExprDefs defmap accum_uses args
            return (accum_fs', accum_uses')

        (inst_fs, letdefs) =
            runCM modId defmap M.empty S.empty $ do
              (fs, uses) <- foldM mkInstField ([], M.empty) (reverse avis)
              ds <- mapM convUse (M.toList uses)
              return (fs, ds)

        ctor_body = sLam ctor_args $
                      sLet letdefs $
                        SStruct (modTypeId modId) (inp_fs ++ inst_fs)
    in
        [SDValue (modCtorId modId) ctor_type ctor_body]

-- -------------------------

makeModDimDefn :: Id -> [AVInst] -> [SDefn]
makeModDimDefn modId avis =
    let
        mod_ty = modType modId []
        dim_type = funcType [mod_ty, mod_ty] boolType

        m1 = mk_homeless_id "mod1"
        m2 = mk_homeless_id "mod2"

        mkInstDim :: AVInst -> SExpr
        mkInstDim avi =
            let
                fname = instFieldId modId (avi_vname avi)
                fvalue1 = SSelect (SVar m1) fname
                fvalue2 = SSelect (SVar m2) fname

                submod = getVNameString (vName (avi_vmi avi))
                submod_dim = SVar $ modDimId (mk_homeless_id submod)
            in
                SApply submod_dim [fvalue1, fvalue2]

        body = sBAnds (map mkInstDim avis)

        dim_body = sLam [(m1,mod_ty), (m2,mod_ty)] body
    in
        [SDValue (modDimId modId) dim_type dim_body]

-- -------------------------

convARule :: DefMap -> InstMap -> MethodOrderMap -> Id -> ARule -> SDefn
convARule defmap instmap mmap modId r@(ARule rId _ _ _ p as _ _) =
  let
      mod_ty = modType modId []

      body = runCM modId defmap instmap S.empty $
                 convActions [] mmap modId p as Nothing
  in
      SDValue (ruleId modId rId) (ruleType mod_ty) $
        SLam stateId mod_ty $
          body

-- -------------------------

convAIFace :: DefMap -> InstMap -> MethodOrderMap ->
              Id -> AIFace -> [SDefn]

convAIFace defmap instmap mmap modId
           (AIDef mId args _ p (ADef _ ret_t ret_e _) _ _) =
  let
      mod_ty = modType modId []
      rt = convAType ret_t

      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      -- get all the defs used by the return value
      uses = getAExprDefs defmap M.empty [ret_e]

      body = runCM modId defmap instmap argset $ do
                 ret_expr <- convAExpr ret_e
                 ds <- mapM convUse (M.toList uses)
                 return $ sLet ds ret_expr
  in
      [SDValue (methId (getIdBaseString modId) mId)
               (valueMethType arg_types mod_ty rt) $
         sLam (arg_infos ++ [(stateId, mod_ty)]) $
           body]

convAIFace defmap instmap mmap modId
           (AIAction args _ p mId rs _) =
  let
      mod_ty = modType modId []

      -- arguments are Bit type
      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      body = runCM modId defmap instmap argset $
               convAIFaceBody mmap modId mId rs Nothing
  in
      [SDValue (methId (getIdBaseString modId) mId)
               (actionMethType arg_types mod_ty voidType) $
         sLam (arg_infos ++ [(stateId, mod_ty)]) $
           body]

convAIFace defmap instmap mmap modId
           (AIActionValue args _ p mId rs (ADef _ def_t def_e _) _) =
  let
      mod_ty = modType modId []
      -- return value is Bit type
      ret_ty = convAType def_t

      -- arguments are Bit type
      argset = S.fromList (map fst args)
      arg_infos = map (\(i,t) -> (methArgId i, convAType t)) args
      arg_types = map snd arg_infos

      body = runCM modId defmap instmap argset $
               convAIFaceBody mmap modId mId rs (Just def_e)
  in
      [SDValue (methId (getIdBaseString modId) mId)
               (actionMethType arg_types mod_ty ret_ty) $
         sLam (arg_infos ++ [(stateId, mod_ty)]) $
           body]

-- ignore clocks, resets, inouts
-- XXX do we need to make clock gates available?
convAIFace _ _ _ _ _ = []


-- the common conversion for the body of Action and ActionValue methods
convAIFaceBody :: MethodOrderMap -> AId -> AId -> [ARule] -> Maybe AExpr ->
                  CM SExpr
convAIFaceBody mmap modId mId rs m_ret = do
  defmap <- gets defMap
  let
      -- get all the defs used in the predicates of the rules
      pred_uses = getAExprDefs defmap M.empty (map arule_pred rs)

      -- conv one rule
      convRule (ARule _ _ _ _ p as _ _) = do
        p_expr <- convAExpr p
        -- convert the body without a predicate (mkATrue)
        -- (and assuming that the pred_uses are already in scope)
        r_upd <- convActions (M.keys pred_uses) mmap modId mkATrue as m_ret
        return (p_expr, r_upd)

      -- fold this in reverse
      foldFn accum r = do
        (p_expr, r_upd) <- convRule r
        return $ sIf p_expr r_upd accum

  -- XXX When there are split rules, the return value is duplicated.
  -- XXX We can lift the return value out, and exclude its uses from
  -- XXX inside the converted bodies.
  case rs of
    [] -> internalError ("convAIFace: no rules: " ++ ppReadable mId)
    -- a special case for one rule might have to check whether the rule's
    -- predicate is True (can we have split rules where one rule is removed,
    -- leaving one rule with a non-True predicate?)
    rs -> do
      -- the predicates in the if-else structure may refer to defs
      ds <- mapM convUse (M.toList pred_uses)
      -- we don't assume that the predicates are complete,
      -- so the final branch is a null update
      rs_expr <- foldM foldFn nullUpdVar (reverse rs)
      return $ sLet ds rs_expr

-- -------------------------

data ConvState =
    ConvState {
        -- the Id of the module being converted
        curModId :: Id,

        defMap :: DefMap,
        instMap :: InstMap,
        -- the arguments to a method, when converting in a method body
        argSet :: S.Set AId,

        -- store of unique numbers for generating let-binding names
        uniqueNum :: Integer,

        -- the current state
        curState :: SExpr,
        -- the current guard
        curGuard :: SExpr
    }

type CM = State ConvState

runCM :: Id -> DefMap -> InstMap -> S.Set AId -> (CM a) -> a
runCM modId defmap instmap argset fn =
    let state0 = ConvState { curModId = modId,
                             defMap  = defmap,
                             instMap = instmap,
                             argSet  = argset,
                             uniqueNum = 1,
                             curState = stateVar,
                             curGuard = trueCon }
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

setGuard :: SExpr -> CM ()
setGuard newGuard = do
  s <- get
  put (s { curGuard = newGuard })

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
convAType (ATTuple ts) = internalError ("convAType: multi-output methods are not yet supported")
convAType t@(ATAbstract {}) = internalError ("convAType: " ++ ppReadable t)

-- -----

convActions :: [AId] -> MethodOrderMap -> AId ->
               AExpr -> [AAction] -> Maybe AExpr ->
               CM SExpr
convActions predefined_defs mmap modId p as m_ret = do
  defmap <- gets defMap

  -- get the current guard/state/num, because we'll be changing them
  prev_guard_expr <- gets curGuard
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

  let_defs <- concatMapM (convStmt modId avmap) ordered_blocks

  -- get the final guard and state
  guard_expr <- gets curGuard
  state_expr <- gets curState

  -- reset the state/guard/num
  setGuard prev_guard_expr
  setState prev_state_expr
  setUniqueNum prev_unique_num

  -- OK to convert the return expression here, because any state
  -- references should have been lifted to their own defs
  ret_expr <- case m_ret of
                Nothing -> return voidCon
                Just ret -> convAExpr ret
  let ret_tup = SApply mktupleVar [sBAnd p_expr guard_expr,
                                   state_expr, ret_expr]

  return $ sLet let_defs ret_tup


-- each statement generates let bindings, and possibly updates the state
-- and guard used by the later statements
convStmt :: AId -> M.Map (AId, AId) (AId, AType) ->
            AStmt -> CM [(Id, SType, SExpr)]

convStmt _ _ (AStmtDef (ADef i t (AMethValue { }) _ )) =
  -- the action will assign the def, so skip it here
  return []

convStmt _ _ (AStmtDef (ADef i t (ATaskValue { }) _ )) =
  -- the action will assign the def, so skip it here
  return []

convStmt _ _ (AStmtDef (ADef i t e _)) = do
  e_expr <- convAExpr e
  return [(defId i, convAType t, e_expr)]

convStmt modId avmap (AStmtAction cset (ACall obj meth as)) = do
  let c = getCondExpr cset

  let mod_type = modType modId []
  instmap <- gets instMap

  -- get the current state/guard, because we'll be changing them
  prev_state <- gets curState
  prev_guard <- gets curGuard

  -- convert the condition
  c_expr <- convAExpr c
  -- convert the arguments
  a_exprs <- mapM convAExpr as

  let
      -- the kind of module that this instance is
      (submod, submod_tys, meth_ty_map) = lookupMod instmap obj
      -- the function name for the method call on this submodule type
      fnname = methId submod meth
      -- the field name for this instance in the state for the current module
      instname = (instFieldId modId obj)
      -- extract the state for this submod instance
      submod_state = SSelect prev_state instname
      -- the type of the submod state
      submod_type = modType (mk_homeless_id submod) submod_tys

      -- get the return type for the action
      -- and if it has a name, then return the def name to bind it to
      (av_type, maybe_av_id) =
          case (M.lookup (obj, meth) avmap) of
            Just (i, t) -> (convAType t, Just (defId i))
            Nothing -> -- no name because the value is unused
                       -- but we still need to declare the correct type
                       case (M.lookup (unQualId meth) meth_ty_map) of
                         Just [t] -> (convAType t, Nothing)
                         Just [] -> (voidType, Nothing)
                         -- TODO: support multiple return values
                         Just ts -> error ("convStmt: multiple return values for method " ++
                                         ppReadable (obj, meth, ts))
                         Nothing -> (voidType, Nothing)

  -- we'll create new defs "act#", "guard#", and "state#" with a unique number
  n  <- getUniqueNum

  -- the method call
  let act_id = mk_homeless_id ("act" ++ itos n)
      act_expr = SApply (SVar fnname) (a_exprs ++ [submod_state])
      act_def = (act_id, tupleType [boolType, submod_type, av_type], act_expr)

  -- the resulting guard
  let guard_id = mk_homeless_id ("guard" ++ itos n)
      -- don't apply the method if the condition is not True
      guard_expr = sIf c_expr
                     (sBAnd prev_guard (SApply fst3Var [SVar act_id]))
                     prev_guard
      guard_def = (guard_id, boolType, guard_expr)

  -- the resulting state
  let state_id = mk_homeless_id ("state" ++ itos n)
      -- don't apply the method if the condition is not True
      state_expr = sIf c_expr
                     (SStructUpd prev_state
                        [(instname, SApply snd3Var [SVar act_id])])
                     prev_state
      state_def = (state_id, mod_type, state_expr)

  -- the return value
  let av_defs = case maybe_av_id of
                  Nothing -> []
                  Just av_id ->
                      let av_expr = SApply thdVar [SVar act_id]
                      in  [(av_id, av_type, av_expr)]

  -- reset the guard and state
  setGuard (SVar guard_id)
  setState (SVar state_id)

  return $ (act_def:guard_def:state_def:av_defs)

convStmt _ _ (AStmtAction cset (AFCall i f isC as isAssumpCheck)) = do
  -- the effect is outside our scope, and there is no return value,
  -- so do nothing
  return []

convStmt _ _ (AStmtAction cset (ATaskAction i f isC k as tmp t b)) = do
  -- the effect is outside our scope, but there is a return value,
  -- so assign it to an unknown value
  case tmp of
    Just i -> let st = convAType t
              in return [(defId i, st, anyTVar st)]
    Nothing ->
        -- its value is unused, so do nothing
        return []

convStmt modId avmap (AStmtIf cset tblk fblk) = do
  let c = getCondExpr cset

  let mod_type = modType modId []

  -- get the current state/guard, because we'll be changing them
  prev_state <- gets curState
  prev_guard <- gets curGuard

  -- convert the condition
  c_expr <- convAExpr c

  -- convert the True branch
  tblk_defs <- concatMapM (convStmt modId avmap) tblk
  -- record the final state/guard for this branch
  true_state <- gets curState
  true_guard <- gets curGuard

  -- convert the False branch, with the original state/guard
  setState prev_state
  setGuard prev_guard
  fblk_defs <- concatMapM (convStmt modId avmap) fblk
  -- record the final state/guard for this branch
  false_state <- gets curState
  false_guard <- gets curGuard

  -- create new defs "guard#" and "state#" for the chosen branch
  n <- getUniqueNum

  -- the resulting guard
  let guard_id = mk_homeless_id ("guard" ++ itos n)
      guard_expr = sIf c_expr true_guard false_guard
      guard_def = (guard_id, boolType, guard_expr)

  -- the resulting state
  let state_id = mk_homeless_id ("state" ++ itos n)
      state_expr = sIf c_expr true_state false_state
      state_def = (state_id, mod_type, state_expr)

  -- reset the guard and state
  setGuard (SVar guard_id)
  setState (SVar state_id)

  return $ tblk_defs ++ fblk_defs ++ [guard_def, state_def]

-- -----

convAExpr :: AExpr -> CM SExpr
convAExpr (ASInt _ t (IntLit _ _ v)) | (t == mkATBool) =
  case v of
    0 -> return falseCon
    1 -> return trueCon
    _ -> internalError ("convAExpr: invalid Bool: " ++ ppReadable v)
convAExpr (ASInt _ (ATBit width) (IntLit _ _ v)) =
  return $ SBVLit width v
convAExpr e@(ASInt {}) =
  internalError ("convAExpr: non-bit ASInt: " ++ ppReadable e)

convAExpr e@(ASStr i t v) =
  return $ SStringLit v

convAExpr e@(ASReal i t v) =
  return $ SRealLit v

convAExpr (ASDef t i) = return $ defVar i

convAExpr (ASPort t i) = do
  modId <- gets curModId
  argset <- gets argSet
  if (S.member i argset)
    then -- just reference the argument
         return $ SVar (methArgId i)
    else -- select the value from the state
         -- XXX since this is read-only, we can take it from the original state
         -- XXX not from the sequenced state?
         return $ SSelect stateVar (portFieldId modId i)
convAExpr (ASParam t i) = do
  modId <- gets curModId
  -- select the value from the state
  -- XXX since this is read-only, we can take it from the original state
  -- XXX not from the sequenced state?
  return $ SSelect stateVar (paramFieldId modId i)

-- if we know what value will be picked, use that
convAExpr (ASAny _ (Just e)) = convAExpr e
-- otherwise, use a primitive to express that it's an unknown
convAExpr (ASAny t Nothing) = let st = convAType t
                              in return $ anyTVar st

convAExpr (APrim _ t p args) = convAPrim p t args

convAExpr (AMethCall _ obj meth as) = do
  modId <- gets curModId
  state_expr <- gets curState
  instmap <- gets instMap
  let (mod, _, _) = lookupMod instmap obj
      mname = methId mod meth
      modState = SSelect state_expr (instFieldId modId obj)
  a_exprs <- mapM convAExpr as
  return $ SApply (SVar mname) (a_exprs ++ [modState])

convAExpr e@(AMethValue t obj meth) =
  -- these are handled by convStmts and are not expected here
  internalError("convAExpr: AMethValue: " ++ ppReadable e)

convAExpr (ATupleSel _ _ _) =
  internalError "convAExpr: multi-output methods are not yet supported"
convAExpr (ATuple {}) =
  internalError "convAExpr: multi-output methods are not yet supported"

convAExpr (ANoInlineFunCall t i (ANoInlineFun name _ _ _) as) = do
  let func_id = noinlineId i
  a_exprs <- mapM convAExpr as
  return $ sApply (SVar func_id) a_exprs

convAExpr (AFunCall t i f isC as) =
  -- probably can't assume anything about two calls with the same arguments,
  -- XXX so don't do anything with "as" here?
  let st = convAType t
  in return $ anyTVar st

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
  let st = convAType t
  in return $ anyTVar st

-- -----

convAPrim :: PrimOp -> AType -> [AExpr] -> CM SExpr
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
  let p_var = SVar (mk_homeless_id "arraySelect")
  return (SApply p_var [arr_expr, idx_expr])

convAPrim PrimBuildArray t as = do
  a_exprs <- mapM convAExpr as
  let sz = case t of
             ATArray n _ -> n
             _ -> internalError ("convAPrim: PrimBuildArray: " ++ ppReadable t)
  let p_var = SVar (mk_homeless_id ("buildArray" ++ show sz))
  return (sApply p_var a_exprs)

-- PrimBAnd and PrimBOr need to be converted to infix operators
-- (in the ASyntax, they can handle variable arguments)
convAPrim PrimBAnd _ as = do
  a_exprs <- mapM convAExpr as
  return (sBAnds a_exprs)
convAPrim PrimBOr _ as = do
  a_exprs <- mapM convAExpr as
  return (sBOrs a_exprs)

-- represent "primBNot" with simple Haskell "not"
convAPrim PrimBNot _ [a] = do
  a_expr <- convAExpr a
  return (sBNot a_expr)

-- PrimConcat needs to be converted to a binary function
-- (in the ASyntax, it can handle variable arguments)
convAPrim p@(PrimConcat) t as = do
  let p_var = primVar p
  a_exprs <- mapM convAExpr as
  return (primBinAps p_var a_exprs)

-- PrimExtract needs a type signature for the result
convAPrim p@(PrimExtract) t as = do
  let p_var = primVar p
      st = convAType t
  a_exprs <- mapM convAExpr as
  return (SHasType st (sApply p_var a_exprs))

convAPrim p _ as = do
  let p_var = primVar p
  a_exprs <- mapM convAExpr as
  return (sApply p_var a_exprs)

-- -----

-- convert the elements of a use map (returned by getAExprDefs etc)
convUse :: (AId, (AType, AExpr)) -> CM (Id, SType, SExpr)
convUse (i, (t, e)) = do
  e' <- convAExpr e
  return (defId i, convAType t, e')

-- -------------------------
