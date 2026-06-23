module Deriving(derive) where

import Control.Monad(when)
import Data.List(intercalate, foldl')
import Util(log2, checkEither, headOrErr, lastOrErr, unconsOrErr, fromJustOrErr)
import Error(internalError, EMsg, WMsg, ErrMsg(..), ErrorHandle,
             bsError, bsWarning)
import Flags(Flags)
import Position
import Id
import PreIds(
              -- identifiers
              tmpTyVarIds, tmpVarXIds, tmpVarYIds, id_x, id_y, idPolyWrapField,
              -- internal type constructors
              idId, idPrimPair, idArrow, idFmt, idMaybe,
              idValid, idInvalid,
              -- internal type fields
              idPrimFst, idPrimSnd,
              -- type constructors
              idBit, idAdd, idMax,
              idConc, idConcPrim, idConcPoly, idMeta,
              idMetaData, idStarArg, idNumArg, idStrArg, idStarConArg, idNumConArg, idOtherConArg,
              idMetaConsNamed, idMetaConsAnon, idMetaField,
              -- classes that the compiler can derive
              idEq, idBits, idValidateBits, idFShow, idBounded, idDefaultValue,
              -- classes that are auto-derived
              autoderivedClasses,
              idGeneric,
              -- internal classes defined in terms of Generic but still occasionally auto-derived
              idClsUninitialized, idUndefined,
              -- class members
              idPack, idUnpack, idUnpackValid,
              idEqual, idNotEqual,
              idfshow,
              idMaxBound, idMinBound,
              id_defaultValue,
              idFrom, idTo,
              -- internal class members
              idPrimMakeUninitialized, idPrimUninitialized,
              idMakeUndef, idBuildUndef,
              -- functions
              idPrimUnitAt,
              idFalse, idTrue, idNot, idAnd,
              idPrimOrd, idPrimChr,
              idPrimSplit, idPrimConcat, idPrimTrunc,
              idFormat,
              )
import CSyntax
import CSyntaxUtil
import CSyntaxTypes
import Type(fn, tBool, tBit)
-- never make a type without a kind in Deriving
-- kind inference has already happened, so don't waste work
import CType hiding (cTVar, cTCon)
import Pred
import Data.Maybe
import PFPrint
import SymTab
import TIMonad
import TCMisc
import FStringCompat

import qualified Data.Set as S

-- import Debug.Trace

-- | Derive instances for all types with deriving (...) in a package, and
-- return the package agumented with the instance definitions.
derive :: ErrorHandle -> Flags -> SymTab -> CPackage -> IO CPackage
derive errh flags r (CPackage i exps imps impsigs fixs ds includes) =
    let all_ds = ds ++ concat [ cs | (CImpSign _ _ (CSignature _ _ _ cs)) <- impsigs ]
        -- Create an environment, that maps IDs to definitions for *all*
        -- top-level definitions (eg value defns, type decls, tyepeclass decls,
        -- instance defns etc). NB we only need the typeclass decls
        env = [ (unQualId i, d) | d <- all_ds, (Right i) <- [getName d] ]
        (warns, results) =
            let perDecl = map (doDer flags r i env) ds
            in  (concatMap fst perDecl, concatMap snd perDecl)
    in  do
          when (not (null warns)) $ bsWarning errh warns
          case checkEither results of
            -- If deriving succeeded, return the updated CPackage with the extra
            -- declarations.
            Right dss'  -> return (CPackage i exps imps impsigs fixs (concat dss') includes)
            Left msgs@(msg:rest) -> bsError errh msgs
            Left [] -> internalError "Deriving.derive: doDer failed with empty error list!]"

-- my guesses at the arguments:
--  packageid  =  id of the package
--  xs =  available bindings
--  d  =  single definition potentially requiring deriving
doDer :: Flags -> SymTab -> Id -> [(Id, CDefn)] -> CDefn ->
         ([WMsg], [Either EMsg [CDefn]])
doDer flags r packageid xs data_decl@(Cdata {}) =
    let unqual_name = iKName (cd_name data_decl)
        qual_name = qualId packageid unqual_name
        kind = case findType r qual_name of
                 Just (TypeInfo _ k _ _ _) -> k
                 _ -> internalError "Deriving.doDer Cdata: findType"
        ty_var_names = cd_type_vars data_decl
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind ty_var_names ty_var_kinds
        orig_sums = cd_original_summands data_decl
        int_sums = cd_internal_summands data_decl
        derivs = cd_derivings data_decl
        derivs' = addAutoDerivs flags r qual_name ty_vars derivs
        warns = derivedValidateBitsWarns qual_name derivs'
    in (warns,
        Right [data_decl] :
        map (doDataDer r packageid xs qual_name ty_vars orig_sums int_sums) derivs')
doDer flags r packageid xs struct_decl@(Cstruct _ s i ty_var_names fields derivs) =
    let unqual_name = iKName i
        qual_name = qualId packageid unqual_name
        kind = case findType r qual_name of
                 Just (TypeInfo _ k _ _ _) -> k
                 _ -> internalError "Deriving.doDer Cstruct: findType"
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind ty_var_names ty_var_kinds
        derivs' = addAutoDerivs flags r qual_name ty_vars derivs
        warns = derivedValidateBitsWarns qual_name derivs'
    in (warns,
        Right [struct_decl] :
        map (doStructDer r packageid xs qual_name ty_vars fields) derivs')
doDer flags r packageid xs prim_decl@(CprimType (IdKind i kind))
    -- "special" typeclasses only need to be derived for ordinary types
    | res_kind /= KStar = ([], [Right [prim_decl]])
    -- Id__ a will pick up typeclass instances from the type a
    | qual_name == idId = ([], [Right [prim_decl]])
    | null derivs = ([], [Right [prim_decl]])
    | otherwise = ([],
                   Right [prim_decl] :
                   map (doPrimTypeDer qual_name ty_vars) derivs)
  where qual_name = qualId packageid i
        res_kind = getResKind kind
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind tmpTyVarIds ty_var_kinds
        derivs = addAutoDerivs flags r qual_name ty_vars []
doDer flags r packageid xs (CprimType idk) =
    internalError ("CprimType no kind: " ++ ppReadable idk)
doDer flags r packageid xs d = ([], [Right [d]])

-- | A derived ValidateBits is compatible with derived Bits, but a
-- hand-written Bits instance is likely not to match.
derivedValidateBitsWarns :: Id -> [CTypeclass] -> [WMsg]
derivedValidateBitsWarns ty_id derivs
    | any (isCls idValidateBits) derivs && not (any (isCls idBits) derivs) =
        let pos = case [ getPosition d | d <- derivs, isCls idValidateBits d ] of
                    (p:_) -> p
                    []    -> getPosition ty_id
        in  [(pos, WDerivedValidateBitsHandwrittenBits (pfpString ty_id))]
    | otherwise = []
  where isCls clsId (CTypeclass di) = qualEq di clsId

doPrimTypeDer :: Id -> [Type] -> CTypeclass -> Either EMsg [CDefn]
doPrimTypeDer i vs (CTypeclass di)
    | qualEq di idGeneric          = Right [doPrimTypeGeneric i vs]
    | otherwise =  internalError ("attempt to derive " ++ ppReadable di
                        ++ " for primitive type: " ++
                        (ppReadable (cTApplys (cTCon i) vs)))

doPrimTypeGeneric :: Id -> [CType] -> CDefn
doPrimTypeGeneric i vs = Cinstance (CQType [] (TAp (TAp (cTCon idGeneric) ty) rep)) [from, to]
  where ty  = cTApplys (cTCon i) vs
        rep = TAp (cTCon idConcPrim) ty
        from = CLValue idFromNQ [CClause [] [] $ CCon idConcPrim []] []
        var = mkId noPosition $ mkFString $ "a"
        to = CLValue idToNQ [CClause [CPCon idConcPrim $ [CPVar var]] [] $ CVar var] []

-- | Derive an instance of a typeclass that the compiler knows about (eg Eq
-- or FShow) for a given data (sum type), and return the instance definitions.
-- my guesses at the arguments:
--  r   =  the current symbol table
--  packageid = id name of the package
--  xs  =  available bindings
--  i   =  qualified id of the data type
--  vs  =  argument type variables of the data type
--  ocs =  original summands of the data type
--         (an id and a list of types of its arguments)
--  cs  =  internal summands of the data type
--         (an id and one type -- the list became a struct)
--  di  =  the class to be derived
doDataDer :: SymTab -> Id -> [(Id, CDefn)] -> Id -> [Type] -> COSummands -> CSummands ->
             CTypeclass -> Either EMsg [CDefn]
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idEq =
  Right [doDEq (getPosition di) i vs ocs cs]
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idBits =
  doDBits (getPosition di) i vs ocs cs
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idValidateBits =
  doDValidateBits (getPosition di) i vs ocs cs
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idBounded =
  Right [doDBounded (getPosition di) i vs ocs cs]
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idDefaultValue =
  Right [doDDefaultValue (getPosition di) i vs ocs cs]
doDataDer _ _ _ i vs ocs cs (CTypeclass di) | qualEq di idFShow =
  Right [doDFShow (getPosition di) i vs ocs cs]
doDataDer r packageid xs i vs ocs cs (CTypeclass di) | qualEq di idGeneric =
  doDGeneric r packageid (getPosition di) i vs ocs
-- If the deriving class is successfully looked up and if it isomorphic to
-- another type, that is it has only one disjunct taking only one argument,
-- then inherit the instance from that type.
doDataDer _ _ xs i vs [cos@(COriginalSummand { cos_arg_types = [CQType _ ty]})] cs di
  | fieldSet `S.isSubsetOf` tvset
  , Just (Cclass _ _ _ [v] _ _ fs) <- lookup (typeclassId di) xs
  = let
        ity = foldl TAp (cTCon i) vs
        inst = Cinstance (CQType [CPred di [ty]] (TAp (cTCon $ typeclassId di) ity)) (map conv fs)
        conv (CField { cf_name = f, cf_type = CQType _ t }) =
            CLValue (unQualId f)
                        [CClause [] []
                         (mkConv con coCon tmpVarXIds tv t (CVar f))] []
          where kind = fromJustOrErr "Deriving.doDataDer isomorphic: getTypeKind" $
                         getTypeKind t
                tv = cTVarKind v kind
        cn = getCOSName cos
        con e = CCon cn [e]
        coCon e = Ccase (getPosition di)
                        e
                        [CCaseArm { cca_pattern = CPCon cn [CPVar id_y],
                                    cca_filters = [],
                                    cca_consequent = CVar id_y }]
    in
        Right [inst]
  where tvset = S.fromList (concatMap tv vs)
        fieldType = cos_arg_types cos
        fieldSet = S.fromList (tv fieldType)
doDataDer _ _ _ i vs ocs cs (CTypeclass di) =
  Left (getPosition di, ECannotDerive (pfpString di))

-- | Derive an instance of a typeclass that the compiler knows about (eg Eq or
-- FShow) for a given struct (prod type), and return the instance definitions.
doStructDer :: SymTab -> Id -> [(Id, CDefn)] -> Id -> [Type] -> CFields -> CTypeclass
            -> Either EMsg [CDefn]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idEq =
  Right [doSEq (getPosition di) i vs cs]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idBits =
  Right [doSBits (getPosition di) i vs cs]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idValidateBits =
  Right [doSValidateBits (getPosition di) i vs cs]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idBounded =
  Right [doSBounded (getPosition di) i vs cs]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idDefaultValue =
  Right [doSDefaultValue (getPosition di) i vs cs]
doStructDer _ _ _ i vs cs (CTypeclass di) | qualEq di idFShow =
  Right [doSFShow (getPosition di) i vs cs]
doStructDer r packageid _ i vs cs (CTypeclass di) | qualEq di idGeneric =
  doSGeneric r packageid (getPosition di) i vs cs
-- If the struct is isomorphic to another type (that is, it as only one
-- field, of that other type), then inherit the instance from that type.
doStructDer _ _ xs i vs [field] di
  | fieldSet `S.isSubsetOf` tvset
  , Just (Cclass _ _ _ [v] _ _ fs) <- lookup (typeclassId di) xs
  = let
        ity = foldl TAp (cTCon i) vs
        CQType _ type_no_qual = fieldType
        inst = Cinstance (CQType [CPred di [type_no_qual]]
                          (TAp (cTCon $ typeclassId di) ity)) (map conv fs)
        conv (CField { cf_name = f, cf_type = CQType _ t }) =
                CLValue (unQualId f) [CClause [] [] (mkConv con coCon tmpVarXIds tv t (CVar f))] []
          where kind = fromJustOrErr "Deriving.doStructDer isomorphic: getTypeKind" $
                         getTypeKind t
                tv = cTVarKind v kind
        con e = CStruct (Just True) i [(cf_name field, e)]
        coCon e = CSelectTT i e (cf_name field)
    in
        Right [inst]
  where tvset = S.fromList (concatMap tv vs)
        fieldType = cf_type field
        fieldSet = S.fromList (tv fieldType)
doStructDer _ _ _ i vs cs (CTypeclass di) | isTCId i =
  -- ignore bad deriving, it should be handled in the data case
  Right []
doStructDer _ _ _ i vs cs (CTypeclass di) =
  Left (getPosition di, ECannotDerive (pfpString di))


-- -------------------------

-- | Derive Eq for a struct (product type), and return the instance definition.
-- Two struct values are equal if all their fields are equal.
doSEq :: Position -> Id -> [Type] -> CFields -> CDefn
doSEq dpos ti vs fs = Cinstance (CQType ctx (TAp (cTCon idEq) ty)) [eq, ne]
  where ctx = map (\ (CField { cf_type = CQType _ t }) -> CPred (CTypeclass idEq) [t]) fs
        ty = cTApplys (cTCon ti) vs
        qt = CQType [] (ty `fn` ty `fn` tBool)
        eq = CLValueSign (CDef (idEqualNQ dpos) qt [eqc]) []
        ne = CLValueSign (CDef (idNotEqualNQ dpos) qt [nec]) []
        eqc = CClause [CPVar id_x, CPVar id_y] [] eqb
        nec = CClause [CPVar id_x, CPVar id_y] [] (eNot (cVApply idEqual [vx, vy]))
        vx = CVar id_x
        vy = CVar id_y
        eqb =
                case fs of
                [] -> eTrue
                fs -> foldr1 eAnd
                      [cVApply idEqual [CSelectTT ti vx (cf_name field),
                                        CSelectTT ti vy (cf_name field)]
                       | field <- fs ]

-- | Derive Eq for a data (sum type), and return the instance definition
-- Two sum type values are equal if they have the same constructor and the
-- constructor args are equal. Enums are handled similarly (but with slight
-- simplification.)
doDEq :: Position -> Id -> [Type] -> COSummands -> CSummands -> CDefn
doDEq dpos i vs ocs cs = Cinstance (CQType ctx (TAp (cTCon idEq) ty)) [eq, ne]
  where ctx | isEnum ocs = []
            | otherwise = concat [(CPred (CTypeclass idEq) [t] : ps) | oc <- ocs, CQType ps t <- cos_arg_types oc  ]
        ty = cTApplys (cTCon i) vs
        qt = CQType [] (ty `fn` ty `fn` tBool)
        eq = CLValueSign (CDef (idEqualNQ dpos) qt [eqc]) []
        ne = CLValueSign (CDef (idNotEqualNQ dpos) qt [nec]) []
        eqc = CClause [CPVar id_x, CPVar id_y] [] eqb
        nec = CClause [CPVar id_x, CPVar id_y] [] (eNot (cVApply idEqual [vx, vy]))
        vx = CVar id_x
        vy = CVar id_y
        eqb | isEnum ocs = cVApply idEqual [hasSz (cVApply idPrimOrd [vx]) sz,
                                            cVApply idPrimOrd [vy]]
            | otherwise =
                Ccase dpos
                      vx
                      (map gen ocs ++
                       [CCaseArm { cca_pattern = CPAny noPosition,
                                   cca_filters = [],
                                   cca_consequent = eFalse }])
        -- max tag: the highest tag encoding
        max_tag | null cs = 0
                | otherwise = foldr1 max $ map cis_tag_encoding cs
        sz = cTNum (log2 $ max_tag + 1) tpos
        gen :: COriginalSummand -> CCaseArm
        gen cos =
            CCaseArm { cca_pattern = CPCon1 i cn (CPVar id_x1),
                       cca_filters = [CQGen noType
                                      (CPCon1 i cn (CPVar id_y1)) vy],
                       cca_consequent = cmp }
                where ts = cos_arg_types cos
                      cn = getCOSName cos
                      n = length ts
                      id_x1 = head tmpVarXIds
                      id_y1 = head tmpVarYIds
                      cmp = if n == 0 then eTrue else cVApply idEqual [CVar id_x1, CVar id_y1]
        tpos = getIdPosition i


-- -------------------------

-- | Build the instance context for deriving Bits or ValidateBits on a struct.
-- For
--     struct S = { a :: T1; b :: T2 } deriving (Bits)
-- returns the context (`Bits T1 sa, Bits T2 sb, Add sa sb sz`) and the total
-- size (`sz`).
structBitsContextAndSize :: Id -> Position -> CFields -> ([CPred], Type)
structBitsContextAndSize clsId pos fields = (ctx, sz)
  where n     = length fields
        avs   = take (n-1) (everyThird tmpTyVarIds)
        bvs   = take n (everyThird (tail tmpTyVarIds))
        aCtx  = if null fields then []
                else let f _ [] _ = []
                         f a (s:ss) (m:mm) =
                             CPred (CTypeclass idAdd)
                                   [cTVarNum s, cTVarNum a, cTVarNum m]
                                 : f m ss mm
                         f _ _ _ = internalError "Deriving.structBitsInstContext.f: _ (_:_) []"
                         (b, bs) = unconsOrErr "Deriving.structBitsInstContext: null bvs" $
                                     reverse bvs
                     in  f b bs avs
        bCtx  = zipWith (\ (CField { cf_type = cqt@(CQType _ t) }) sv ->
                          CPred (CTypeclass clsId)
                                [t, cTVarNum (setIdPosition (getPosition cqt) sv)])
                        fields bvs
        cCtx  = concatMap (\ (CField { cf_type = CQType q _}) -> q) fields
        ctx   = bCtx ++ aCtx ++ cCtx
        sz    = case fields of
                  []  -> cTNum 0 pos
                  [_] -> cTVarNum (setIdPosition pos (headOrErr "structBitsInstContext" bvs))
                  _   -> cTVarNum (setIdPosition pos (lastOrErr "structBitsInstContext" avs))

-- | Single primSplit as a continuation-passing primitive. Builds
--     let v = primSplit e in <k v.fst v.snd>
-- where the caller supplies a fresh `v` and a continuation that uses the two
-- halves. Multiple splits compose by nesting splitBit calls inside the
-- continuation. The widths of the halves are determined by the surrounding
-- context via primSplit's `Add n m k` proviso, not by this helper.
splitBit :: CExpr -> Id -> (CExpr -> CExpr -> CExpr) -> CExpr
splitBit e v k = monoDef v (cVApply idPrimSplit [e]) $
                   k (CSelectTT idPrimPair (CVar v) idPrimFst)
                     (CSelectTT idPrimPair (CVar v) idPrimSnd)

-- | Derive Bits for a struct (product type), and return the instance defn.
-- Recursively pack/unpack each field, and concatenate/split the results.
doSBits :: Position -> Id -> [Type] -> CFields -> CDefn
doSBits dpos ti vs fields = Cinstance (CQType ctx (cTApplys (cTCon idBits) [aty, sz])) [pk, un]
  where tiPos = getPosition ti
        (ctx, sz) = structBitsContextAndSize idBits tiPos fields
        aty = cTApplys (cTCon ti) vs
        bty = TAp (cTCon idBit) sz
        vx = CVar id_x

        pkb = case fields of
                [] -> anyExprAt tiPos
                _  -> foldr1 eConcat
                      [cVApply idPack [CSelectTT ti vx (cf_name field)]
                       | field <- fields]
        pkc = CClause [CPVar id_x] [] pkb
        pk  = CLValueSign (CDef (idPackNQ dpos) (CQType [] (aty `fn` bty)) [pkc]) []

        goUnpack acc bs []     _      = CStruct (Just True) ti (reverse acc)
        goUnpack acc bs [f]    _      = CStruct (Just True) ti $ reverse $
                                          (cf_name f, cVApply idUnpack [bs]) : acc
        goUnpack acc bs (f:rest) (v:vs) =
            splitBit bs v $ \slice next ->
              goUnpack ((cf_name f, cVApply idUnpack [slice]) : acc) next rest vs
        goUnpack _ _ _ _ = internalError "Deriving.doSBits.goUnpack: empty supply"
        ukb = goUnpack [] vx fields tmpVarXIds
        unc = CClause [CPVar id_x] [] ukb
        un  = CLValueSign (CDef (idUnpackNQ dpos) (CQType [] (bty `fn` aty)) [unc]) []


-- | Number of bits needed to represent the tag of a tagged union with the
-- given constructors (using their assigned tag values).
dataNumTagBits :: Position -> CSummands -> Type
dataNumTagBits pos tags = cTNum (log2 (max_tag + 1)) pos
  where max_tag = foldl' max 0 [cis_tag_encoding tag | tag <- tags]

-- | Build the instance context for deriving Bits or ValidateBits on a tagged
-- union. For
--     data T = C1 T1 | C2 T2 deriving (Bits)
-- this drives:
--     instance (Bits T1 sa, Bits T2 sb, ...) => Bits T sz
-- where sz = log2(num ctors) + max(sa, sb). Returns the context (the provisos
-- before `=>`), the total size (`sz`), and the per-summand payload size type
-- variables (`[sa, sb, …]`) for callers that need to reference them in the
-- generated pack/unpack body. The clsId argument selects between Bits and
-- ValidateBits.
dataBitsInstContextAndSizes :: Id -> Position -> CSummands
                          -> ([CPred], Type, [Type])
dataBitsInstContextAndSizes clsId pos tags =
    (provisos, num_rep_bits_ctype, payload_sizes)
  where fix_position    = setIdPosition pos
        make_num_vars n l = map (cTVarNum . fix_position) $ take n l
        num_tags        = length tags
        num_tag_bits_ctype = dataNumTagBits pos tags
        -- three disjoint streams of fresh ids (different mod-3 phases)
        sofar_supply    = everyThird tmpTyVarIds
        field_supply    = everyThird (tail tmpTyVarIds)
        padding_supply  = everyThird (tail (tail tmpTyVarIds))
        payload_sizes   = make_num_vars num_tags field_supply
        (num_rep_bits_var, max_payload_size_sofar_vars) =
            unconsOrErr "Deriving.dataBitsInstContextAndSize: sofar_supply" $
              make_num_vars num_tags sofar_supply
        max_num_payload_bits    = last max_payload_size_sofar_vars
        payload_size_paddings = make_num_vars num_tags padding_supply
        (final_bit_size_provisos, num_rep_bits_ctype) =
            case tags of
              []  -> ([], cTNum 0 pos)
              [_] -> ([], headOrErr "dataBitsInstContextAndSize" payload_sizes)
              _   -> ([CPred (CTypeclass idAdd)
                             [num_tag_bits_ctype, max_num_payload_bits, num_rep_bits_var]],
                      num_rep_bits_var)
        payload_bits_provisos =
            zipWith (\ field sv -> CPred (CTypeclass clsId) [cis_arg_type field, sv])
                    tags payload_sizes
        max_payload_size_add_provisos
             | num_tags <= 1 = []
             | otherwise =
               zipWith (\ x sv -> CPred (CTypeclass idAdd) [x, sv, max_num_payload_bits])
                       payload_size_paddings payload_sizes
        max_payload_size_max_provisos
             | null tags = []
             | otherwise =
                 let f _ [] _ = []
                     f a (s:ss) (m:mm) =
                         CPred (CTypeclass idMax) [s, a, m] : f m ss mm
                     f _ _ _ = internalError "Deriving.dataBitsInstContextAndSize.f: _ (_:_) []"
                     (b, bs) = unconsOrErr "Deriving.dataBitsInstContextAndSize: null payload_sizes" $
                                 reverse payload_sizes
                 in  f b bs max_payload_size_sofar_vars
        provisos = payload_bits_provisos ++ max_payload_size_add_provisos ++
                   max_payload_size_max_provisos ++ final_bit_size_provisos

-- | Build the case-on-tag dispatch shared by unpack and unpackValid for a
-- tagged union. mkConsequent decides what each tag arm produces — for Bits
-- it's `Ci (unpack body)`, for ValidateBits it's an unpackValid chain wrapped
-- in Valid. extraArms is appended after the per-tag arms (used by
-- ValidateBits to add a wildcard returning Invalid for sparse tag values).
dataBitsUnpackClauses :: Position -> Position -> CSummands -> Type
                      -> (CInternalSummand -> CExpr -> CExpr) -> [CCaseArm]
                      -> [CClause]
dataBitsUnpackClauses dpos pos tags num_tag_bits_ctype
                      mkConsequent extraArms
    | length tags == 1 =
        [CClause [CPVar id_x] [] $
         mkConsequent (headOrErr "dataBitsUnpackClauses" tags) vx]
    | otherwise =
        [CClause [CPVar id_x] [] $
         monoDef id_y (cVApply idPrimSplit [vx]) $
         Ccase dpos
               (hasSz (CSelectTT idPrimPair vy idPrimFst) num_tag_bits_ctype)
               (map mkArm tags ++ extraArms)]
  where vx       = CVar id_x
        vy       = CVar id_y
        bodyExpr = cVApply idPrimTrunc [CSelectTT idPrimPair vy idPrimSnd]
        mkArm tag = CCaseArm
            { cca_pattern    = CPLit (num_to_cliteral_at pos (cis_tag_encoding tag))
            , cca_filters    = []
            , cca_consequent = mkConsequent tag bodyExpr }

-- | Derive Bits instance for a data (sum) type, with the pack and unpack
-- functions. The packing for a data type consists of a tag and a body. The tag
-- size is log2(n) bits when there are n constructors, and the constructors are
-- numbered from 0 in order of appearance). The body is the packing of each of
-- a constructor's fields concatenated from left to right. When the constructor
-- bodies are not all the same length, they are left padded to the length of
-- the longest body.
-- An enum is like a degenerate form of data type where none of the constructors
-- have a body, and with the added flexibility that the user can specify the
-- tag for a given value.
-- Data tags aren't dense (i.e. don't cover all possible bit encodings) unless
-- there are 2^n constructors, and additionally enum tags may be sparse if
-- the user specifies gaps in the tags.
doDBits :: Position -> Id -> [Type] -> COSummands -> CSummands ->
           Either EMsg [CDefn]
doDBits dpos type_name type_vars original_tags tags
    | not (null (duplicate_tag_encoding_errors type_name tags)) =
        Left (head (duplicate_tag_encoding_errors type_name tags))
doDBits dpos enum_name type_vars original_tags tags
    | isEnum original_tags =
    -- simple case where the fields are just tags, so the number of bits
    -- required to represent the data type is known statically, so
    -- no provisos are required and encoding does not recurse
    let -- unpacked_ctype: original enum type
        unpacked_ctype = cTApplys (cTCon enum_name) type_vars
        -- # of bits required to represent the tag (i.e., the enum type)
        num_bits_ctype = dataNumTagBits (getPosition enum_name) tags
        -- packed_ctype: Bit n (n bits required to represent the enum)
        packed_ctype = TAp (cTCon idBit) num_bits_ctype
        pack_function =
            CDef (idPackNQ dpos) (CQType [] (unpacked_ctype `fn` packed_ctype))
            pack_body
        pack_body = [CClause [] [] (cVar idPrimOrd)]
        unpack_function =
            CDef (idUnpackNQ dpos) (CQType [] (packed_ctype `fn` unpacked_ctype))
                 unpack_body
        -- unpack optimized for [0, 1, ..] (better hardware)
        unpack_body = [CClause [] [] (cVar idPrimChr)]
    in  -- instance Bits unpacked_ctype num_bits_ctype where ...
        Right $
        [Cinstance
         (CQType [] (cTApplys (cTCon idBits) [unpacked_ctype, num_bits_ctype]))
         [CLValueSign pack_function [], CLValueSign unpack_function []]]
doDBits dpos type_name type_vars original_tags tags =
    let decl_position = getPosition type_name
        unpacked_ctype = cTApplys (cTCon type_name) type_vars
        num_tags = length tags
        num_tag_bits_ctype = dataNumTagBits decl_position tags
        (provisos, num_rep_bits_ctype, payload_sizes) =
            dataBitsInstContextAndSizes idBits decl_position tags
        packed_ctype = TAp (cTCon idBit) num_rep_bits_ctype
        vx = CVar id_x

        pkBody sz = cVApply idPrimConcat [anyExprAt decl_position,
                                          hasSz (cVApply idPack [vx]) sz]
        mkArm tag field_sz = CCaseArm
            { cca_pattern    = CPCon1 type_name (getCISName tag) (CPVar id_x)
            , cca_filters    = []
            , cca_consequent = pkBody field_sz }
        tag_expr  = hasSz (cVApply idPrimOrd [vx]) num_tag_bits_ctype
        body_expr = Ccase decl_position vx $ zipWith mkArm tags payload_sizes
        pack_clauses
            | num_tags == 1 =
                [CClause [CPCon1 type_name
                          (getCISName (headOrErr "doDBits" tags)) (CPVar id_x)] []
                 (cVApply idPack [vx])]
            | otherwise = [CClause [CPVar id_x] [] (cVApply idPrimConcat [tag_expr, body_expr])]
        pack_function =
            CDef (idPackNQ dpos) (CQType [] (unpacked_ctype `fn` packed_ctype))
                 pack_clauses

        unpack_type     = CQType [] (packed_ctype `fn` unpacked_ctype)
        unpack_clauses  =
            dataBitsUnpackClauses dpos decl_position tags num_tag_bits_ctype
                (\ tag bodyExpr -> CCon1 type_name (getCISName tag) (cVApply idUnpack [bodyExpr]))
                []
        unpack_function = CDef (idUnpackNQ dpos) unpack_type unpack_clauses
    in  Right
        [Cinstance (CQType provisos (cTApplys (cTCon idBits) [unpacked_ctype, num_rep_bits_ctype]))
         [CLValueSign pack_function [], CLValueSign unpack_function []]]

hasSz :: CExpr -> Type -> CExpr
hasSz e s = CHasType e (CQType [] (TAp tBit s))

-- | Build "case e of { Valid v -> body; Invalid -> Invalid }".
-- Used in derived ValidateBits to thread Invalid through a chain of field
-- validations.
eMaybeBind :: Position -> CExpr -> Id -> CExpr -> CExpr
eMaybeBind pos e v body =
    Ccase pos e
        [ CCaseArm { cca_pattern    = CPCon idValid [CPVar v]
                   , cca_filters    = []
                   , cca_consequent = body }
        , CCaseArm { cca_pattern    = CPCon idInvalid []
                   , cca_filters    = []
                   , cca_consequent = mkMaybe Nothing }
        ]

-- | Derive ValidateBits for a struct, by chaining unpackValid over each field.
-- The result is Valid only if every field validates. For
--     struct S = { a :: T1; b :: T2 } deriving (ValidateBits)
-- the generated unpackValid is roughly:
--     unpackValid bs = case unpackValid (slice for a) of
--                        Valid a' -> case unpackValid (slice for b) of
--                                      Valid b' -> Valid (S { a = a'; b = b' })
--                                      Invalid -> Invalid
--                        Invalid -> Invalid
--
-- We do not implement unpack in terms of unpackValid: unpack returns a partial
-- result with bottoms only where forced, while unpackValid returns Invalid at
-- the top level on any failure, losing the partial result.
doSValidateBits :: Position -> Id -> [Type] -> CFields -> CDefn
doSValidateBits dpos ti vs fields =
    Cinstance (CQType ctx (cTApplys (cTCon idValidateBits) [aty, sz])) [un]
  where (ctx, sz) = structBitsContextAndSize idValidateBits (getPosition ti) fields
        aty = cTApplys (cTCon ti) vs
        bty = TAp (cTCon idBit) sz
        mty = TAp (cTCon idMaybe) aty

        fieldVars = zip fields tmpVarYIds
        result    = mkMaybe $ Just $ CStruct (Just True) ti
                      [(cf_name f, CVar v) | (f, v) <- fieldVars]

        chain _  []             _      = result
        chain bs [(_, v)]       _      =
            eMaybeBind dpos (cVApply idUnpackValid [bs]) v result
        chain bs ((_, v):rest)  (x:xs) =
            splitBit bs x $ \slice next ->
              eMaybeBind dpos (cVApply idUnpackValid [slice]) v $
                chain next rest xs
        chain _ _ _ = internalError "Deriving.doSValidateBits.chain: empty supply"

        unc = CClause [CPVar id_x] [] (chain (CVar id_x) fieldVars tmpVarXIds)
        un  = CLValueSign (CDef (idUnpackValidNQ dpos)
                                (CQType [] (bty `fn` mty)) [unc]) []

-- | Derive ValidateBits for a tagged union. unpackValid dispatches on the tag
-- bits: defined tags chain unpackValid over the body and wrap in Valid; sparse
-- tag values fall through to Invalid. For
--     data T = C1 T1 | C2 T2 deriving (ValidateBits)
-- the dispatch is:
--     case tag of
--       0 -> case unpackValid body of
--              Valid v -> Valid (C1 v)
--              Invalid -> Invalid
--       1 -> case unpackValid body of
--              Valid v -> Valid (C2 v)
--              Invalid -> Invalid
--       _ -> Invalid
-- For an enum (no bodies) each defined tag maps directly to Valid Ci.
--
-- See doSValidateBits for why unpack is not implemented in terms of
-- unpackValid.
doDValidateBits :: Position -> Id -> [Type] -> COSummands -> CSummands ->
                   Either EMsg [CDefn]
doDValidateBits _ type_name _ _ tags
    | not (null (duplicate_tag_encoding_errors type_name tags)) =
        Left (head (duplicate_tag_encoding_errors type_name tags))
doDValidateBits dpos enum_name type_vars original_tags tags
    | isEnum original_tags =
    let epos           = getPosition enum_name
        unpacked_ctype = cTApplys (cTCon enum_name) type_vars
        num_bits_ctype = dataNumTagBits epos tags
        packed_ctype   = TAp (cTCon idBit) num_bits_ctype
        result_ctype   = TAp (cTCon idMaybe) unpacked_ctype
        unpack_function =
            CDef (idUnpackValidNQ dpos)
                 (CQType [] (packed_ctype `fn` result_ctype))
                 [CClause [CPVar id_x] []
                    (Ccase epos (CVar id_x) (map mkArm tags ++ [wildcard]))]
        wildcard = CCaseArm { cca_pattern    = CPAny epos
                            , cca_filters    = []
                            , cca_consequent = mkMaybe Nothing }
        mkArm tag = CCaseArm
            { cca_pattern    = CPLit (num_to_cliteral_at epos
                                       (cis_tag_encoding tag))
            , cca_filters    = []
            , cca_consequent = mkMaybe (Just (CCon (getCISName tag) [])) }
    in  Right
        [Cinstance
         (CQType [] (cTApplys (cTCon idValidateBits)
                              [unpacked_ctype, num_bits_ctype]))
         [CLValueSign unpack_function []]]
doDValidateBits dpos type_name type_vars original_tags tags =
    let decl_position = getPosition type_name
        unpacked_ctype = cTApplys (cTCon type_name) type_vars
        num_tag_bits_ctype = dataNumTagBits decl_position tags
        (provisos, num_rep_bits_ctype, _) =
            dataBitsInstContextAndSizes idValidateBits decl_position tags
        packed_ctype = TAp (cTCon idBit) num_rep_bits_ctype
        result_ctype = TAp (cTCon idMaybe) unpacked_ctype
        body_var     = headOrErr "doDValidateBits: tmpVarYIds" tmpVarYIds

        unpack_clauses =
            dataBitsUnpackClauses dpos decl_position tags num_tag_bits_ctype
                (\ tag bodyExpr ->
                    eMaybeBind decl_position
                               (cVApply idUnpackValid [bodyExpr])
                               body_var
                               (mkMaybe (Just (CCon1 type_name (getCISName tag)
                                                     (CVar body_var)))))
                [CCaseArm { cca_pattern    = CPAny decl_position
                          , cca_filters    = []
                          , cca_consequent = mkMaybe Nothing }]
        unpack_function = CDef (idUnpackValidNQ dpos)
                               (CQType [] (packed_ctype `fn` result_ctype))
                               unpack_clauses
    in  Right
        [Cinstance (CQType provisos
                     (cTApplys (cTCon idValidateBits)
                               [unpacked_ctype, num_rep_bits_ctype]))
         [CLValueSign unpack_function []]]


-- -------------------------

-- | Derive FShow for a struct (product type), and return the instance defn.
-- FShow is the name of each field followed by show of its value, all wrapped
-- in braces.
doSFShow :: Position -> Id -> [Type] -> CFields -> CDefn
doSFShow dpos ti vs fields =
    Cinstance (CQType ctx (cTApplys (cTCon idFShow) [aty])) [fshow_function]
  where
        ctx = bCtx ++ cCtx
        cCtx = concatMap (\ (CField { cf_type = CQType q _}) -> q) fields
        bCtx = map (\ (CField { cf_type = cqt@(CQType _ t) }) ->
                        CPred (CTypeclass idFShow) [t])
                   fields

        aty = cTApplys (cTCon ti) vs
        fty = cTCon idFmt

        fshow_function =
            CLValueSign
                (CDef (idfshowNQ dpos)
                      (CQType [] (aty `fn` fty))
                      [fshow_clause])
                []
        fshow_clause = CClause [CPVar id_x] [] fshow_body

        vx = CVar id_x
        fshow_body =
            let sid = getIdBaseString ti
            in  CTaskApply (CVar idFormat) $
                    [ stringLiteralAt dpos (sid ++ " { ") ] ++
                    field_fmts ++
                    [ stringLiteralAt dpos
                          (case fields of
                             [] -> "}"
                             _ -> " }") ]

        field_fmts =
            let mkFieldFmt field =
                    let fid = cf_name field
                        fstr = getIdBaseString fid
                    in
                        [ stringLiteralAt dpos (fstr ++ ": "),
                          cVApply idfshow [CSelectTT ti vx (cf_name field)] ]
                sepstr = stringLiteralAt dpos ", "
            in  intercalate [sepstr] $ map mkFieldFmt fields


-- | Derive FShow for a data (sum type), and return the instance definition.
-- FShow is the constructor name followed by show of each constructor arg
-- in braces.
doDFShow :: Position -> Id -> [Type] -> COSummands -> CSummands -> CDefn
doDFShow dpos enum_name type_vars original_tags tags
    | isEnum original_tags =
    let
        enum_ctype = cTApplys (cTCon enum_name) type_vars
        fmt_ctype = cTCon idFmt

        fshow_function =
            CLValueSign
                (CDef (idfshowNQ dpos)
                      (CQType [] (enum_ctype `fn` fmt_ctype))
                      fshow_body)
                []

        fshow_body = [ mk_fshow_clause tag | tag <- tags]
        mk_fshow_clause tag =
            let tag_id = getCISName tag
                tag_str = getIdBaseString tag_id
                enum_pattern =
                    [CPCon1 enum_name tag_id
                     (CPstruct (Just True) (idPrimUnitAt dpos) [])]
                fmt_expr =
                    CTaskApply (CVar idFormat) [ stringLiteralAt dpos tag_str ]
            in  CClause enum_pattern [] fmt_expr
    in
        Cinstance
            (CQType [] (cTApplys (cTCon idFShow) [enum_ctype]))
            [fshow_function]
doDFShow dpos union_name type_vars original_tags tags =
    let
        union_ctype = cTApplys (cTCon union_name) type_vars
        fmt_ctype = cTCon idFmt

        provisos =
            let mkProviso f = CPred (CTypeclass idFShow) [cis_arg_type f]
            in  map mkProviso tags

        fshow_function =
            CLValueSign
                (CDef (idfshowNQ dpos)
                      (CQType [] (union_ctype `fn` fmt_ctype))
                      fshow_body)
                []

        fshow_body = [ mk_fshow_clause tag | tag <- tags]
        mk_fshow_clause tag =
            let tag_id = getCISName tag
                tag_str = getIdBaseString tag_id
                union_pattern =
                    [CPCon1 union_name tag_id (CPVar id_x)]
                -- XXX if the associated value is void/unit then don't display?
                fmt_expr =
                    CTaskApply (CVar idFormat)
                        [ stringLiteralAt dpos ("tagged " ++ tag_str ++ " "),
                          cVApply idfshow [CVar id_x] ]
            in  CClause union_pattern [] fmt_expr
    in
        Cinstance
            (CQType provisos (cTApplys (cTCon idFShow) [union_ctype]))
            [fshow_function]


-- -------------------------

-- | Derive the Bounded instance for a data (sum type), and return the instance
-- definition. The min/max is the first/last constructor, with the min/max of
-- each constructor arg, if present.
doDBounded :: Position -> Id -> [Type] -> COSummands -> CSummands -> CDefn
doDBounded dpos i vs ocs cs =
    --if not (all (null . snd) ocs)
    --then compileError ("Cannot derive Bounded for " ++ show i)
    --else
        Cinstance (CQType ctx (TAp (cTCon idBounded) aty)) [maxB, minB]
  where -- this is more restrictive than it needs to be (insisting on Bounded for each term, not just the first and last
        -- this is motivated by what Bounded "should" mean rather than the current requirements of the Bounded class
        ctx | isEnum ocs = []
            | otherwise = [CPred (CTypeclass idBounded) [cis_arg_type field] | field <- cs]
        aty = cTApplys (cTCon i) vs

        -- need to special-case if the constructor takes no arguments
        firstEmpty = (null . cos_arg_types) (headOrErr "doDBounded" ocs)
        lastEmpty = (null . cos_arg_types) (lastOrErr "doDBounded" ocs)
        minBVal = if firstEmpty
                  then (CCon (getCISName (headOrErr "doDBounded" cs)) [])
                  else (CCon1 i (getCISName (headOrErr "doDBounded" cs)) (CVar idMinBound))
        maxBVal = if lastEmpty
                  then (CCon (getCISName (lastOrErr "doDBounded" cs)) [])
                  else (CCon1 i (getCISName (lastOrErr "doDBounded" cs)) (CVar idMaxBound))
        minB = CLValueSign (CDef (idMinBoundNQ dpos) (CQType [] aty) [CClause [] [] minBVal]) []
        maxB = CLValueSign (CDef (idMaxBoundNQ dpos) (CQType [] aty) [CClause [] [] maxBVal]) []

doDDefaultValue :: Position -> Id -> [Type] -> COSummands -> CSummands -> CDefn
doDDefaultValue dpos i vs ocs (cs : _) = Cinstance (CQType ctx (TAp (cTCon idDefaultValue) ty)) [def]
  where ctx   = [ CPred (CTypeclass idDefaultValue) [getRes (cis_arg_type cs)] ]
        ty    = cTApplys (cTCon i) vs
        body  = CCon1 i (getCISName cs) (CVar id_defaultValue)
        def   = CLValueSign (CDef id_defaultValueNQ (CQType [] ty) [CClause [] [] body]) []
doDDefaultValue dpos i vs ocs [] = internalError ("Data type has no constructors: " ++ ppReadable (dpos, i, vs))

doDGeneric :: SymTab -> Id -> Position -> Id -> [Type] -> COSummands -> Either EMsg [CDefn]
doDGeneric r packageid dpos i vs ocs = mkGenericInstance r packageid dpos i vs True
  [(cn, mfns, ftys) | COriginalSummand {cos_names=cn:_, cos_arg_types=ftys, cos_field_names=mfns} <- ocs]

-- -------------------------

-- | Derive Bounded for a struct (product type), and return the definition of
-- the instance.
-- The min/max for a struct is the min/max for each of its fields.
doSBounded :: Position -> Id -> [Type] -> CFields -> CDefn
doSBounded dpos i vs fs = Cinstance (CQType ctx (TAp (cTCon idBounded) aty)) [maxB, minB]
  where aty = cTApplys (cTCon i) vs
        ctx = map (\ (CField {cf_type = CQType _ t}) -> CPred (CTypeclass idBounded) [t]) fs
        minB = mmDef (idMinBoundNQ dpos) idMinBound
        maxB = mmDef (idMaxBoundNQ dpos) idMaxBound
        mmDef md mv =
            let mfs = [ (cf_name f, CVar mv) | f <- fs ]
                str = CStruct (Just True) i mfs
            in        CLValueSign (CDef md (CQType [] aty) [CClause [] [] str]) []

doSDefaultValue :: Position -> Id -> [Type] -> CFields -> CDefn
doSDefaultValue dpos i vs fs = Cinstance (CQType ctx (TAp (cTCon idDefaultValue) ty)) [def]
  where ctx = map (\ (CField {cf_type = CQType _ t}) -> CPred (CTypeclass idDefaultValue) [t]) fs
        ty  = cTApplys (cTCon i) vs
        str = CStruct (Just True) i [ (cf_name f, CVar id_defaultValue) | f <- fs ]
        def = CLValueSign (CDef id_defaultValueNQ (CQType [] ty) [CClause [] [] str]) []

doSGeneric :: SymTab -> Id -> Position -> Id -> [Type] -> CFields -> Either EMsg [CDefn]
doSGeneric r packageid dpos i vs fs = mkGenericInstance r packageid dpos i vs False
  [(i, Just [fn | CField {cf_name=fn} <- fs], [fty | CField {cf_type=fty} <- fs])]

-- Build an instance of Generic for a struct / data declaration,
-- along with any needed poly field wrapper structs and instances
-- Arguments:
--   r == the symbol table
--   packageid == the name of the package
--   dpos == the position of the struct / data declaration
--   i == the name of the struct / data type
--   vs == the type parameters to which the type is applied
--   isData == is the type a data declaration (vs. struct)
--   summands == a list of tuples (constructor name, field names if constructor has named fields, field types)
mkGenericInstance :: SymTab -> Id -> Position -> Id -> [Type] -> Bool -> [(Id, Maybe [Id], [CQType])] ->
                     Either EMsg [CDefn]
mkGenericInstance r packageid dpos i vs isData summands =
  fmap concat $ sequence $ wrapDcls ++ [Right [inst]]
  where ty  = cTApplys (cTCon i) vs
        tvset = S.fromList (tv ty)

        fieldHigherRank :: CQType -> Bool
        fieldHigherRank fty = not $ S.fromList (tv fty) `S.isSubsetOf` tvset

        preds = concat [ps | (_, _, ftys) <- summands, fty@(CQType ps _) <- ftys,
                        not $ fieldHigherRank fty]

        fieldNames (Just fns) dpos = fns
        fieldNames Nothing dpos = [mk_dangling_id ("_" ++ show (k :: Int)) dpos
                                  | k <- [1..]]  -- Infinite stream, but OK since this is always zipped with a list of field types

        wrapDcls = concat [mkGenericRepWrap r dpos i isData cn fn vs fty
                          | (cn, mfns, ftys) <- summands,
                            (fn, fty@(CQType ps _)) <- zip (fieldNames mfns dpos) ftys,
                            fieldHigherRank fty]
        rep = cTApplys (cTCon idMeta)
          [cTApplys (cTCon idMetaData)
           [cTStr (getIdBase i) dpos,
            cTStr (getIdBase packageid) dpos,
            tMkTuple dpos
             [case getTypeKind v of
                Just KStar -> cTApplys (cTCon idStarArg) [v]
                Just KNum -> cTApplys (cTCon idNumArg) [v]
                Just KStr -> cTApplys (cTCon idStrArg) [v]
                Just (Kfun KStar KStar) -> cTApplys (cTCon idStarConArg) [v]
                Just (Kfun KNum KStar) -> cTApplys (cTCon idNumConArg) [v]
                _ -> cTCon idOtherConArg
             | v <- vs],
            cTNum (toInteger $ length summands) dpos],
           tMkEitherTree dpos
            [cTApplys (cTCon idMeta)
              [cTApplys (cTCon $ case mfns of
                            Just _ -> idMetaConsNamed
                            Nothing -> idMetaConsAnon)
                [cTStr (getIdBase cn) dpos,
                  cTNum k dpos,
                  cTNum (toInteger $ length ftys) dpos],
                tMkTuple dpos
                [cTApplys (cTCon idMeta)
                  [cTApplys (cTCon idMetaField)
                    [cTStr (getIdBase fn) dpos, cTNum j dpos],
                    (if fieldHigherRank fty
                     then TAp (cTCon idConcPoly) $
                      cTApplys (cTCon $ genericRepWrapName dpos i isData cn fn) vs
                     else TAp (cTCon idConc) ty)]
                | (j, fn, fty@(CQType _ ty)) <- zip3 [0..] (fieldNames mfns dpos) ftys]]
            | (k, (cn, mfns, ftys)) <- zip [0..] summands]]
        from = CLValue idFromNQ
          [CClause [if isData
                    then CPCon1 i cn (CPVar id_x)
                    else CPVar id_x] [] $
           CCon idMeta
            [mkEitherTree dpos k (length summands) $
             CCon idMeta
              [mkTuple dpos
               [CCon idMeta
                [if fieldHigherRank fty
                 then CCon idConcPoly
                  [CStruct (Just True)
                    (genericRepWrapName dpos i isData cn fn)
                    [(idPolyWrapField, CSelect (CVar id_x) fn)]]
                 else CCon idConc [if isJust mfns || length ftys > 1
                                   then CSelect (CVar id_x) fn
                                   else CVar id_x]]
               | (fn, fty) <- zip (fieldNames mfns dpos) ftys]]]
          | (k, (cn, mfns, ftys)) <- zip [0..] summands] []
        to = CLValue idToNQ
          [CClause
           [CPCon idMeta
            [pMkEitherTree dpos k (length summands) $
             CPCon idMeta
              [pMkTuple dpos
               [CPCon idMeta
                [CPCon (if fieldHigherRank fty then idConcPoly else idConc)
                 [CPVar $ mkId dpos $ mkFString $ "a" ++ show (j :: Int)]]
               | (j, fty) <- zip [1..] ftys]]]] [] $
            let args = [
                  if fieldHigherRank fty
                  then CSelect (CVar $ mkId dpos $ mkFString $ "a" ++ show j) idPolyWrapField
                  else CVar $ mkId dpos $ mkFString $ "a" ++ show (j :: Int)
                  | (j, fty) <- zip [1..] ftys]
            in case mfns of
              Nothing -> CCon cn args
              Just fns -> CStruct (Just (not isData)) cn $ zip fns args
          | (k, (cn, mfns, ftys)) <- zip [0..] summands] []
        inst = Cinstance (CQType preds (TAp (TAp (cTCon idGeneric) ty) rep)) [from, to]

-- Build a wrapper struct for generic representation of a polymorphic field.
-- Otherwise it isn't possible to handle such fields genericly, as the
-- representation type would contain free polymorphic type variables.
-- Arguments:
--   r == the symbol table
--   pos == the position of the struct / data declaration
--   tid == the name of the struct / data type containing the wrapped field
--   isData == is the type a data declaration (vs. struct)
--   cid == the name of the constructor containing the wrapped field
--   fid == the name of the wrapped field
--   ty_vars == the non-polymorphic type variables in the wrapped type
--   fty == the type of the wrapped field
mkGenericRepWrap :: SymTab -> Position -> Id -> Bool -> Id -> Id -> [Type] -> CQType ->
                    [Either EMsg [CDefn]]
mkGenericRepWrap r pos tid isData cid fid ty_vars fty =
  [Right [Cstruct True
          (SPolyWrap tid (if isData then Just cid else Nothing) fid)
          (IdK $ addIdProp i IdPInternal) vs fields []],
   -- Need to generate instances of PrimMakeUninitialized, PrimMakeUndefined and PrimDeepSeqCond
   -- for the wrapper, since the ConcPoly instances call to these through the evaluator primitives
   Right [
      Cinstance (CQType [] (TAp (cTCon idClsUninitialized) (cTApplys (cTCon i) ty_vars)))
        [CLValue idMakeUninitializedNQ
          [CClause [CPVar id_x, CPVar id_y] []
            (CStruct (Just True) i [(idPolyWrapField, CApply (CVar idPrimUninitialized) [CVar id_x, CVar id_y])])] []],
      Cinstance (CQType [] (TAp (cTCon idUndefined) (cTApplys (cTCon i) ty_vars)))
        [CLValue idMakeUndefinedNQ
          [CClause [CPVar id_x, CPVar id_y] []
            (CStruct (Just True) i [(idPolyWrapField, CApply (CVar idBuildUndef) [CVar id_x, CVar id_y])])] []]]]
  where i = genericRepWrapName pos tid isData cid fid
        vs = map (getTyVarId . head . tv) ty_vars
        fields =
          [CField {cf_name = idPolyWrapField,
                   cf_pragmas = Nothing,
                   cf_type = fty,
                   cf_default = [],
                   cf_orig_type = Nothing}]

-- Get the name of the generated wrapper struct
genericRepWrapName :: Position -> Id -> Bool -> Id -> Id -> Id
genericRepWrapName pos tid isData cid fid = mkId pos $ concatFString $
  [getIdBase tid, mkFString "_"] ++
  (if isData then [getIdBase cid, mkFString "_"] else []) ++
  [getIdBase fid]

-- -------------------------

eNot :: CExpr -> CExpr
eNot e = cVApply idNot [e]
eAnd :: CExpr -> CExpr -> CExpr
eAnd e1 e2 = cVApply idAnd [e1, e2]
eConcat :: CExpr -> CExpr -> CExpr
eConcat e1 e2 = cVApply idPrimConcat [e1, e2]

eTrue, eFalse :: CExpr
eTrue = CCon idTrue []
eFalse = CCon idFalse []

monoDef :: Id -> CExpr -> CExpr -> CExpr
monoDef v b e = CApply (CLam (Right v) e) [b]

everyThird :: [Id] -> [Id]
everyThird (x:_:_:xs) = x : everyThird xs
everyThird [] = internalError "Deriving.everyThird: []"
everyThird [_] = internalError "Deriving.everyThird: [_]"
everyThird [_,_] = internalError "Deriving.everyThird: [_,_]"

-- these identifiers are explicitly unqualified because we do not know
-- what packages instances for struct or union components are found
idEqualNQ :: Position -> Id
idEqualNQ pos = setIdPosition pos (unQualId idEqual)
idNotEqualNQ :: Position -> Id
idNotEqualNQ pos = setIdPosition pos (unQualId idNotEqual)
idPackNQ :: Position -> Id
idPackNQ pos = setIdPosition pos (unQualId idPack)
idUnpackNQ :: Position -> Id
idUnpackNQ pos = setIdPosition pos (unQualId idUnpack)
idUnpackValidNQ :: Position -> Id
idUnpackValidNQ pos = setIdPosition pos (unQualId idUnpackValid)
idfshowNQ :: Position -> Id
idfshowNQ pos = setIdPosition pos (unQualId idfshow)
idMaxBoundNQ :: Position -> Id
idMaxBoundNQ pos = setIdPosition pos (unQualId idMaxBound)
idMinBoundNQ :: Position -> Id
idMinBoundNQ pos = setIdPosition pos (unQualId idMinBound)
id_defaultValueNQ :: Id
id_defaultValueNQ = unQualId id_defaultValue
idMakeUndefinedNQ :: Id
idMakeUndefinedNQ = unQualId idMakeUndef
idMakeUninitializedNQ :: Id
idMakeUninitializedNQ = unQualId idPrimMakeUninitialized
idFromNQ :: Id
idFromNQ = unQualId idFrom
idToNQ :: Id
idToNQ = unQualId idTo

----

mkConv :: (CExpr -> CExpr) -> (CExpr -> CExpr) -> [Id] -> CType -> CType -> (CExpr -> CExpr)
mkConv con coCon _ v v' | v == v' = con
mkConv con coCon (x:xs) v (TAp (TAp (TCon (TyCon arr _ _)) a) r) | arr == idArrow noPosition =
        \ e -> CLam (Right x)
                 (mkConv con coCon xs v r
                    (CApply e [mkConv coCon con xs v a (CVar x)]))
mkConv _ _ _ v t = \ e -> e

-- generate errors for duplicate tag encodings
duplicate_tag_encoding_errors :: Id -> [CInternalSummand] -> [EMsg]
duplicate_tag_encoding_errors type_name [] = []
duplicate_tag_encoding_errors type_name (tag:rest_tags) =
    duplicate_tag_encoding_error type_name tag rest_tags ++
    duplicate_tag_encoding_errors type_name rest_tags

-- generate errors for encodings conflicting with that of the current tag
duplicate_tag_encoding_error :: Id -> CInternalSummand -> [CInternalSummand]
                             -> [EMsg]
duplicate_tag_encoding_error type_name tag rest_tags
    | null duplicate_tags = []
    | otherwise = [(getPosition tag,
                    EOverlappingTagEncoding (getIdBaseString type_name)
                    (cis_tag_encoding tag) (first_tag:duplicate_tags))]
    where first_tag = (getPosition tag, pfpString (getCISName tag))
          duplicate_tags =
              [(getPosition next_tag, pfpString (getCISName next_tag))
               | next_tag <- rest_tags,
                 cis_tag_encoding next_tag == cis_tag_encoding tag]

addAutoDeriv :: Flags -> SymTab -> Id -> [CType] -> Id -> [CTypeclass]
                 -> [CTypeclass]
addAutoDeriv flags r i tvs clsId derivs
                         -- incoherent matches are resolved *after* reducePred
    | (Right True, _, _) <- runTI flags False r check = derivs
  where check = do
          let (kind, sort) =
                  -- trace ("check undef: " ++ show clsId) $
                  case findType r i of
                    Just (TypeInfo _ k _ s _) -> (k, s)
                    _ -> internalError "Deriving.addAutoDeriv: findType"
          let t = cTApplys (TCon (TyCon i (Just kind) sort)) tvs
          cls <- findCls (CTypeclass clsId)
          -- Look for an instance where the first parameter is the specified type
          -- and any remaining parameters are filled in with variables.
          -- This is needed for Generic.
          vp <- mkVPredFromPred [] (IsIn cls $ t : (map TVar $ tail $ csig cls))
          -- if there is an existing undefined instance, the predicate will reduce
          mreduce <- reducePred [] Nothing vp
          -- trace (show clsId ++ ": " ++ ppReadable mreduce) $
          return (isJust mreduce)

addAutoDeriv flags r i tvs clsId derivs =
  -- trace ("auto-derive: " ++ ppReadable (clsId, i))
  (CTypeclass clsId) : derivs

-- All types are automatically given instances for the typeclasses in
-- autoderivedClasses if an explicit instance isn't provided by the user.
-- Implement this by adding the classes to the derive list for each type.
addAutoDerivs :: Flags -> SymTab -> Id -> [CType] -> [CTypeclass]
                  -> [CTypeclass]
addAutoDerivs flags r i tvs derivs =
  -- trace ("autoderivedClasses for " ++ show i ++ ": " ++ ppReadable autoderivedClasses) $
  foldr (f . setPos) derivs autoderivedClasses
   where pos    = getIdPosition i
         setPos clsId = setIdPosition pos (unQualId clsId)
         f = addAutoDeriv flags r i tvs


-- -------------------------
