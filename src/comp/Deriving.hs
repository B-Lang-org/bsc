{-# LANGUAGE PatternGuards #-}
module Deriving(derive) where

import Data.List(nub, intercalate)
import Util(log2, checkEither, unions, toMaybe, headOrErr, lastOrErr)
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle, bsError)
import Flags(Flags)
import Position
import Id
import PreIds(
              -- identifiers
              tmpTyVarIds, tmpVarXIds, tmpVarYIds, id_x, id_y,
              id_forallb,
              -- internal type constructors
              idId, idPrimPair, idArrow, idFmt,
              -- internal type fields
              idPrimFst, idPrimSnd,
              -- internal classes to auto-derive
              idUndefined, idClsUninitialized, idClsDeepSeqCond,
              requiredClasses,
              -- internal class members
              idPrimUninitialized, idPrimMakeUninitialized, idPrimRawUninitialized,
              idPrimSeqCond, idPrimDeepSeqCond,
              idRawUndef, idMakeUndef, idBuildUndef,
              -- type constructors
              idBit, idAdd, idMax,
              -- classes
              idEq, idBits, idFShow, idBounded,
              -- class members
              idPack, idUnpack,
              idPreludePlus, idEqual, idNotEqual,
              idfshow,
              idMaxBound, idMinBound,
              -- functions
              idPrintType,
              idPrimError,
              idPrimUnit, idPrimUnitAt,
              idFalse, idTrue, idNot, idAnd,
              idPrimOrd, idPrimChr,
              idPrimSplit, idPrimConcat, idPrimTrunc,
              idFormat,
              )
import CSyntax
import CSyntaxUtil
import CSyntaxTypes
import Type(fn, tBool, tBit, tPosition, tInteger, tString)
-- never make a type without a kind in Deriving
-- kind inference has already happened, so don't waste work
import CType hiding (cTVar, cTCon)
import Pred
import Data.Maybe
import PFPrint
import SymTab
import TIMonad
import TCMisc

import qualified Data.Set as S

-- import Trace
-- import Debug.Trace

derive :: ErrorHandle -> Flags -> SymTab -> CPackage -> IO CPackage
derive errh flags r (CPackage i exps imps fixs ds includes) =
    let all_ds = ds ++ concat [ cs | (CImpSign _ _ (CSignature _ _ _ cs)) <- imps ]
        env = [ (unQualId i, d) | d <- all_ds, (Right i) <- [getName d] ]
    in  case checkEither (concatMap (doDer flags r i env) ds) of
          Right ds  -> return (CPackage i exps imps fixs (concat ds) includes)
          Left msgs@(msg:rest) -> bsError errh msgs
          Left [] -> internalError "Deriving.derive: doDer failed with empty error list!]"

-- my guesses at the arguments:
--  packageid  =  id of the package
--  xs =  available bindings
--  d  =  single definition potentially requiring deriving
doDer :: Flags -> SymTab -> Id -> [(Id, CDefn)] -> CDefn ->
         [Either EMsg [CDefn]]
doDer flags r packageid xs data_decl@(Cdata {}) =
    let unqual_name = iKName (cd_name data_decl)
        qual_name = qualId packageid unqual_name
        Just (TypeInfo _ kind _ _) = findType r qual_name
        ty_var_names = cd_type_vars data_decl
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind ty_var_names ty_var_kinds
        orig_sums = cd_original_summands data_decl
        int_sums = cd_internal_summands data_decl
        derivs = cd_derivings data_decl
        derivs' = addRequiredDerivs flags r qual_name ty_vars derivs
        -- XXX ignore derivs' to sneak in recursive data decls
        bad_rec_derivs = filter forbidsRecursiveInstance derivs
    in  if (not (null bad_rec_derivs)) && (isRecursiveData unqual_name orig_sums)
        then [Left (getPosition data_decl,
                    EDeriveRecursive (map (getIdString . typeclassId) bad_rec_derivs) (getIdString unqual_name))]
        else Right [data_decl] :
               map (doDataDer xs qual_name ty_vars orig_sums int_sums) derivs'
doDer flags r packageid xs struct_decl@(Cstruct _ s i ty_var_names fields derivs) =
    let unqual_name = iKName i
        qual_name = qualId packageid unqual_name
        Just (TypeInfo _ kind _ _) = findType r qual_name
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind ty_var_names ty_var_kinds
        derivs' = addRequiredDerivs flags r qual_name ty_vars derivs
        bad_rec_derivs = filter forbidsRecursiveInstance derivs'
    in  if (not (null bad_rec_derivs)) && (isRecursiveStruct unqual_name fields)
        then [Left (getPosition struct_decl,
                    EDeriveRecursive (map (getIdString . typeclassId) bad_rec_derivs) (getIdString unqual_name))]
        else Right [struct_decl] :
               map (doStructDer xs qual_name ty_vars fields) derivs'
doDer flags r packageid xs prim_decl@(CprimType (IdKind i kind))
    -- "special" typeclasses only need to be derived for ordinary types
    | res_kind /= KStar = [Right [prim_decl]]
    -- Id__ a will pick up typeclass instances from the type a
    | qual_name == idId = [Right [prim_decl]]
    | null derivs = [Right [prim_decl]]
    | otherwise = Right [prim_decl] :
                     map (doPrimTypeDer qual_name ty_vars) derivs
  where qual_name = qualId packageid i
        res_kind = getResKind kind
        ty_var_kinds = getArgKinds kind
        ty_vars = zipWith cTVarKind tmpTyVarIds ty_var_kinds
        derivs = addRequiredDerivs flags r qual_name ty_vars []
doDer flags r packageid xs (CprimType idk) =
    internalError ("CprimType no kind: " ++ ppReadable idk)
doDer flags r packageid xs d = [Right [d]]

doPrimTypeDer :: Id -> [Type] -> CTypeclass -> Either EMsg [CDefn]
doPrimTypeDer i vs (CTypeclass di)
    | qualEq di idUndefined        = Right [doPrimTypeUndefined i vs]
    | qualEq di idClsUninitialized = Right [doPrimTypeUninitialized i vs]
    | qualEq di idClsDeepSeqCond   = Right [doPrimTypeDeepSeqCond i vs]
    | otherwise =  internalError ("attempt to derive " ++ ppReadable di
                        ++ " for primitive type: " ++
                        (ppReadable (cTApplys (cTCon i) vs)))

rawUninitDef :: Type -> CDef
rawUninitDef ty = CDef idMakeUninitializedNQ (CQType [] aty) [CClause [] [] (CVar idPrimRawUninitialized)]
  where aty = tPosition `fn` tString `fn` ty

doPrimTypeUninitialized :: Id -> [CType] -> CDefn
doPrimTypeUninitialized i vs = Cinstance (CQType [] (TAp (cTCon idClsUninitialized) ty)) [uninit]
  where ty = cTApplys (cTCon i) vs
        uninit = CLValueSign (rawUninitDef ty) []

ty_forallb :: Type
ty_forallb = t `fn` t
  where t = cTVar id_forallb

doPrimTypeUndefined :: Id -> [CType] -> CDefn
doPrimTypeUndefined i vs = Cinstance (CQType [] (TAp (cTCon idUndefined) ty)) [undef]
  where ty  = cTApplys (cTCon i) vs
        aty = tPosition `fn` tInteger `fn` ty
        undef = CLValueSign (CDef idMakeUndefinedNQ (CQType [] aty) [CClause [CPVar id_x, CPVar id_y] [] body]) []
        body = cVApply idPrimError [CVar id_x, str_expr]
        str_expr = cVApply idPreludePlus [error_str, type_str]
        error_str = stringLiteralAt noPosition "Attempt to use undetermined "
        type_str = cVApply idPrintType [typeLiteral ty]

doPrimTypeDeepSeqCond :: Id -> [CType] -> CDefn
doPrimTypeDeepSeqCond i vs = Cinstance (CQType [] (TAp (cTCon idClsDeepSeqCond) ty)) [dseqcond]
  where ty  = cTApplys (cTCon i) vs
        def_ty = CQType [] (ty `fn` ty_forallb)
        dseqcond = CLValueSign (CDef idPrimDeepSeqCondNQ def_ty [CClause [] [] body]) []
        body = CVar idPrimSeqCond

-- recursive deriving of Bits causes an error in the typechecking phase
-- of the compiler
-- Because this is identically False, (it used to be True), the code that depends
-- on it may be safely removed at some point.
forbidsRecursiveInstance :: CTypeclass -> Bool
forbidsRecursiveInstance i = False

isRecursiveData :: Id -> COSummands -> Bool
isRecursiveData i ocs =
    let allCQTyCons (CQType _ ty) = allTConNames ty
        types = unions (map (cos_arg_types) ocs)
        cons = unions (map allCQTyCons types)
    in  i `elem` cons

isRecursiveStruct :: Id -> CFields -> Bool
isRecursiveStruct i fs =
    let allCQTyCons (CQType _ ty) = allTConNames ty
        cons = unions (map (allCQTyCons . cf_type) fs)
    in  i `elem` cons

-- my guesses at the arguments:
--  xs  =  available bindings
--  i   =  qualified id of the data type
--  vs  =  argument type variables of the data type
--  ocs =  original summands of the data type
--         (an id and a list of types of its arguments)
--  cs  =  internal summands of the data type
--         (an id and one type -- the list became a struct)
--  di  =  the class to be derived
doDataDer :: [(Id, CDefn)] -> Id -> [Type] -> COSummands -> CSummands ->
             CTypeclass -> Either EMsg [CDefn]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idEq =
  Right [doDEq (getPosition di) i vs ocs cs]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idBits =
  doDBits (getPosition di) i vs ocs cs
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idBounded =
  Right [doDBounded (getPosition di) i vs ocs cs]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idFShow =
  Right [doDFShow (getPosition di) i vs ocs cs]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idUndefined =
  Right [doDUndefined i vs ocs cs]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idClsUninitialized =
  Right [doDUninitialized i vs ocs cs]
doDataDer xs i vs ocs cs (CTypeclass di) | qualEq di idClsDeepSeqCond =
  Right [doDDeepSeqCond i vs ocs cs]
-- If the deriving class is successfully looked up and if it isomorphic to
-- another type, that is it has only one disjunct taking only one argument,
-- then inherit the instance from that type.
doDataDer xs i vs [cos@(COriginalSummand { cos_arg_types = [CQType _ ty]})] cs di
    | fieldSet `S.isSubsetOf` tvset,
      Just (Cclass _ _ _ [v] _ fs) <- lookup (typeclassId di) xs = Right [inst]
  where tvset  = S.fromList (concatMap tv vs)
        fieldType = cos_arg_types cos
        fieldSet = S.fromList (tv fieldType)
        Just (Cclass _ _ _ [v] _ fs) = lookup (typeclassId di) xs
        ity = foldl TAp (cTCon i) vs
        inst = Cinstance (CQType [CPred di [ty]] (TAp (cTCon $ typeclassId di) ity)) (map conv fs)
        conv (CField { cf_name = f, cf_type = CQType _ t }) =
            CLValue (unQualId f)
                        [CClause [] []
                         (mkConv con coCon tmpVarXIds tv t (CVar f))] []
          where (Just kind) = getTypeKind t
                tv = cTVarKind v kind
        cn = getCOSName cos
        con e = CCon cn [e]
        coCon e = Ccase (getPosition di)
                        e
                        [CCaseArm { cca_pattern = CPCon cn [CPVar id_y],
                                    cca_filters = [],
                                    cca_consequent = CVar id_y }]
doDataDer xs i vs ocs cs (CTypeclass di) =
  Left (getPosition di, ECannotDerive (pfpString di))

doStructDer :: [(Id, CDefn)] -> Id -> [Type] -> CFields -> CTypeclass
            -> Either EMsg [CDefn]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idEq =
  Right [doSEq (getPosition di) i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idBits =
  Right [doSBits (getPosition di) i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idBounded =
  Right [doSBounded (getPosition di) i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idFShow =
  Right [doSFShow (getPosition di) i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idUndefined =
  Right [doSUndefined i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idClsUninitialized =
  Right [doSUninitialized i vs cs]
doStructDer _ i vs cs (CTypeclass di) | qualEq di idClsDeepSeqCond =
  Right [doSDeepSeqCond i vs cs]
-- If the struct is isomorphic to another type (that is, it as only one
-- field, of that other type), then inherit the instance from that type.
doStructDer xs i vs [field] di
    | fieldSet `S.isSubsetOf` tvset,
      Just (Cclass _ _ _ [v] _ fs) <- lookup (typeclassId di) xs = Right [inst]
  where tvset  = S.fromList (concatMap tv vs)
        fieldType = cf_type field
        fieldSet = S.fromList (tv fieldType)
        Just (Cclass _ _ _ [v] _ fs) = lookup (typeclassId di) xs
        ity = foldl TAp (cTCon i) vs
        CQType _ type_no_qual = fieldType
        inst = Cinstance (CQType [CPred di [type_no_qual]]
                          (TAp (cTCon $ typeclassId di) ity)) (map conv fs)
        conv (CField { cf_name = f, cf_type = CQType _ t }) =
                CLValue (unQualId f) [CClause [] [] (mkConv con coCon tmpVarXIds tv t (CVar f))] []
          where (Just kind) = getTypeKind t
                tv = cTVarKind v kind
        con e = CStruct i [(cf_name field, e)]
        coCon e = CSelectTT i e (cf_name field)
doStructDer _ i vs cs (CTypeclass di) | isTCId i =
  -- ignore bad deriving, it should be handled in the data case
  Right []
doStructDer _ i vs cs (CTypeclass di) =
  Left (getPosition di, ECannotDerive (pfpString di))


-- -------------------------

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
        sz = cTNum (log2 (length ocs)) tpos
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

doSBits :: Position -> Id -> [Type] -> CFields -> CDefn
doSBits dpos ti vs fields = Cinstance (CQType ctx (cTApplys (cTCon idBits) [aty, sz])) [pk, un]
  where tiPos = getPosition ti
        ctx = bCtx ++ aCtx ++ cCtx
        cCtx = concatMap (\ (CField { cf_type = CQType q _}) -> q) fields
        bCtx = zipWith (\ (CField { cf_type = cqt@(CQType _ t) }) sv ->
                        CPred (CTypeclass idBits)
                                  [t, cTVarKind
                                      (setIdPosition (getPosition cqt) sv)
                                      KNum]) fields bvs
        aCtx = let f _ [] _ = []
                   f a (s:ss) (n:nn) =
                       CPred (CTypeclass idAdd)
                                 [cTVarKind s KNum, cTVarKind a KNum,
                                  cTVarKind n KNum] : f n ss nn
                   f _ _ _ = internalError "Deriving.doSBits.f: _ (_:_) []"
                   b:bs = reverse bvs
                in if null fields then [] else f b bs avs
        avs = take (n-1) (everyThird tmpTyVarIds)
        bvs = take n (everyThird (tail tmpTyVarIds))
        sz = case fields of
                [] -> cTNum 0 tiPos
                [_] -> cTVarKind (setIdPosition tiPos (headOrErr "doSBits" bvs)) KNum
                _   -> cTVarKind (setIdPosition tiPos (lastOrErr "doSBits" avs)) KNum
        aty = cTApplys (cTCon ti) vs
        bty = TAp (cTCon idBit) sz
        n = length fields

        pk = CLValueSign (CDef (idPackNQ dpos) (CQType [] (aty `fn` bty)) [pkc]) []
        pkc = CClause [CPVar id_x] [] pkb
        vx = CVar id_x
        pkb = case fields of
                [] -> anyExprAt tiPos
                _  -> foldr1 eConcat
                      [cVApply idPack [CSelectTT ti vx (cf_name field)]
                       | field <- fields]

        un = CLValueSign (CDef (idUnpackNQ dpos) (CQType [] (bty `fn` aty)) [unc]) []
        unc = CClause [CPVar id_x] [] ukb
        ukb = case fields of
                [] -> CStruct ti []
                [field] -> CStruct ti [(cf_name field, cVApply idUnpack [vx])]
                _  -> let xs = take (n-1) tmpVarXIds
                          bind = mkBind vx xs
                          mkBind o [] = id
                          mkBind o (x:xs) =
                                monoDef x (cVApply idPrimSplit [o]) .
                                mkBind (CSelectTT idPrimPair (CVar x) idPrimSnd) xs
                          mkExp [field] y _ =
                              [(cf_name field, cVApply idUnpack
                                [CSelectTT idPrimPair (CVar y) idPrimSnd])]
                          mkExp (field:fields) y (x:xs) =
                              (cf_name field, cVApply idUnpack
                               [CSelectTT idPrimPair (CVar x) idPrimFst]) :
                              mkExp fields x xs
                          mkExp _ _ _ = internalError "Deriving.doSBits.ukb.mkExp: [] _ _ or _ _ []"
                          err = internalError "Deriving.doSBits.ukb.mkExp: no var"
                      in  bind (CStruct ti (mkExp fields err xs))


-- doDBits: derive Bits instance, with the pack and unpack functions,
--          for a enum or tagged union declaration
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
        -- highest tag encoding
        max_tag | null tags = 0
                | otherwise = foldr1 max [cis_tag_encoding tag | tag <- tags]
        is_contiguous = contiguousTags tags
        -- # of bits required to represent the tag (i.e., the enum type)
        num_bits_ctype = cTNum (log2 (max_tag + 1)) (getPosition enum_name)
        -- packed_ctype: Bit n (n bits required to represent the enum)
        packed_ctype = TAp (cTCon idBit) num_bits_ctype
        pack_function =
            CDef (idPackNQ dpos) (CQType [] (unpacked_ctype `fn` packed_ctype))
            pack_body
        -- pack optimized for [0, 1, ..] (better hardware)
        pack_body | is_contiguous = [CClause [] [] (cVar idPrimOrd)]
                  | otherwise = [mk_pack_clause tag | tag <- tags]
        mk_pack_clause tag = -- clause for a specific tag
            let unpacked_pattern =
                    [CPCon1 enum_name (getCISName tag)
                     (CPstruct (idPrimUnitAt (getPosition tag)) [])]
                packed_expr =
                    hasSz (CLit (num_to_cliteral_at (getPosition tag)
                                 (cis_tag_encoding tag))) num_bits_ctype
            in  CClause unpacked_pattern [] packed_expr
        unpack_function =
            CDef (idUnpackNQ dpos) (CQType [] (packed_ctype `fn` unpacked_ctype))
                 unpack_body
        -- unpack optimized for [0, 1, ..] (better hardware)
        unpack_body | is_contiguous = [CClause [] [] (cVar idPrimChr)]
                    | otherwise = [mk_unpack_clause tag | tag <- tags]
        mk_unpack_clause tag = -- clause for a specific tag
            let packed_pattern = [CPLit (num_to_cliteral_at (getPosition tag)
                                         (cis_tag_encoding tag))]
                unpacked_expr =
                    CCon1 enum_name (getCISName tag) (CStruct idPrimUnit [])
            in  CClause packed_pattern [] unpacked_expr
    in  -- instance Bits unpacked_ctype num_bits_ctype where ...
        Right $
        [Cinstance
         (CQType [] (cTApplys (cTCon idBits) [unpacked_ctype, num_bits_ctype]))
         [CLValueSign pack_function [], CLValueSign unpack_function []]]
doDBits dpos type_name type_vars original_tags tags =
    -- default case where fields contain data in addition to tags: provisos
    -- are required to compute the final bit size
    let -- decl_position: where the original type was declared
        decl_position = getPosition type_name
        -- fix_position: point an id at the type for which we're deriving
        fix_position = setIdPosition decl_position
        -- make_num_vars: turn a list of ids into usable numeric types
        -- fix their position and mark them as KNum
        make_num_vars n l = map (cTVarNum . fix_position) $ take n l
        -- type_ctype: the csyntax type for which we're deriving
        unpacked_ctype = cTApplys (cTCon type_name) type_vars
        -- num_tags: number of tags in the tagged union
        num_tags = length tags
        -- max tag: the highest tag encoding
        max_tag | null tags = 0
                | otherwise = foldr1 max [cis_tag_encoding tag | tag <- tags]
        -- num_tag_bits_ctype: the number of bits required to represent the tag
        num_tag_bits_ctype = cTNum (log2 (max_tag + 1)) decl_position
        -- provisos constraining the final bit size
        provisos = fields_provisos_bits ++ max_field_size_add_provisos ++
                   max_field_size_max_provisos ++ final_bit_size_provisos
        -- make sure all subfields can be turned into bits
        fields_provisos_bits =
            zipWith (\ field sv -> CPred (CTypeclass idBits) [cis_arg_type field, sv])
                    tags field_bit_sizes
        -- max_field_size_provisos constrain max_num_field_bits to an
        --   upper bound of all subfield sizes by context:
        --       add freshvar sizeof(field) max_num_field_bits
        max_field_size_add_provisos
             | num_tags <= 1 = []
             | otherwise =
               zipWith ( \ x sv ->
                         CPred (CTypeclass idAdd)
                                   [x, sv, max_num_field_bits])
                       field_bit_size_paddings field_bit_sizes
        -- max_field_size_max_provisos constrain max_num_field_bits to
        --   the least upper bound of all subfield sizes by constraining
        --   lastvar to be the largest
        max_field_size_max_provisos
             | null tags = []
             | otherwise =
                 let f _ [] _ = []
                     f a (s:ss) (n:nn) =
                         CPred (CTypeclass idMax) [s, a, n] : f n ss nn
                     f _ _ _ = internalError "Deriving.doDBits.f: _ (_:_) []"
                     b:bs = reverse field_bit_sizes
                 in  f b bs max_field_size_sofar_vars
        num_rep_bits_var:max_field_size_sofar_vars =
            make_num_vars num_tags (everyThird tmpTyVarIds)
        -- max_num_field_bits: # bits required to represent all fields w/o tags
        max_num_field_bits = last max_field_size_sofar_vars
        -- field_bit_sizes: the bit sizes of the fields (as CTypes)
        field_bit_sizes = make_num_vars num_tags (everyThird (tail tmpTyVarIds))
        -- field_bit_size_paddings: padding between individual field size
        --   and the maximum field size; used only once, as dummy variables
        field_bit_size_paddings = make_num_vars num_tags (everyThird (tail (tail tmpTyVarIds)))
        -- final_bit_size_provisos constrain the final bit size of the
        --   tagged union: tag size + max(field sizes) = final size
        -- num_rep_bits_ctype: the final bit size of the tagged union
        (final_bit_size_provisos, num_rep_bits_ctype) =
                case original_tags of
                []  -> ([], cTNum 0 decl_position)
                [_] -> ([], headOrErr "doDBits" field_bit_sizes)
                _   -> ([CPred (CTypeclass idAdd)
                                   [num_tag_bits_ctype,
                                    max_num_field_bits,
                                    num_rep_bits_var]],
                        num_rep_bits_var)
        packed_ctype = TAp (cTCon idBit) num_rep_bits_ctype
        pack_function =
            CDef (idPackNQ dpos) (CQType [] (unpacked_ctype `fn` packed_ctype))
                 pack_clauses
        pack_clauses
            | num_tags == 1 =
                [CClause [CPCon1 type_name
                          (getCISName (headOrErr "doDBits" tags)) (CPVar id_x)] []
                 (cVApply idPack [vx])]
            | otherwise = zipWith mkPk tags field_bit_sizes ++ [packLast]
        mkPk tag field_sz =
            CClause [CPCon1 type_name (getCISName tag) (CPVar id_x)] []
                        (cVApply idPrimConcat
                         [litSz (cis_tag_encoding tag), pkBody field_sz])

        -- Construct a custom fallthrough case to help (pack . unpack)
        -- optimize to the identity. Explicitly using anyExpr instead of relying
        -- on the UNoMatch case inserted by IConv means that this undetermined value
        -- will not optimize away during static elaboration, preserving structure
        -- that ITransform can rebuild into an identity.
        -- The explicit tag ++ payload concatenation is not strictly necessary,
        -- but should help make the reconstruction more robust now that
        -- improveIf in IExpand can merge matching bit concatenations.
        packLast = CClause [CPAny decl_position] []
                           (cVApply idPrimConcat
                                    [ hasSz (anyExprAt decl_position) num_tag_bits_ctype
                                    , anyExprAt decl_position
                                    ])

        pkBody sz = cVApply idPrimConcat [anyExprAt decl_position,
                                          hasSz (cVApply idPack [vx]) sz ]
        litSz k = hasSz (CLit $ num_to_cliteral_at decl_position k)
                  num_tag_bits_ctype

        unpack_function = CDef (idUnpackNQ dpos) unpack_type unpack_clauses
        unpack_type = CQType [] (packed_ctype `fn` unpacked_ctype)
        unpack_clauses
            -- if there's only one, unpack the contents
            | num_tags == 1 = [CClause [CPVar id_x] [] (CCon1 type_name (getCISName (headOrErr "doDBits" tags))
                                                  (cVApply idUnpack [vx]))]
             | otherwise = [CClause [CPVar id_x] []
                            (monoDef id_y (cVApply idPrimSplit [vx]) $
                             Ccase dpos
                                   (hasSz (CSelectTT idPrimPair vy idPrimFst)
                                    num_tag_bits_ctype)
                                   (map mkUn tags))]
        mkUn tag =
            CCaseArm { cca_pattern = CPLit (num_to_cliteral_at decl_position
                                            (cis_tag_encoding tag)),
                       cca_filters = [],
                       cca_consequent = (CCon1 type_name (getCISName tag)
                                         unBody) }
        unBody = cVApply idUnpack [cVApply idPrimTrunc
                                   [CSelectTT idPrimPair vy idPrimSnd]]
        vx = CVar id_x
        vy = CVar id_y
    in  Right $
        [Cinstance (CQType provisos
                    (cTApplys (cTCon idBits) [unpacked_ctype,
                                              num_rep_bits_ctype]))
         [CLValueSign pack_function [], CLValueSign unpack_function []]]

hasSz :: CExpr -> Type -> CExpr
hasSz e s = CHasType e (CQType [] (TAp tBit s))


-- -------------------------

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
                     (CPstruct (idPrimUnitAt dpos) [])]
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

doDUndefined :: Id -> [Type] -> COSummands -> CSummands -> CDefn
-- the single-summand case is not already derived for data declarations with no internal type
-- e.g. ActionWorld
doDUndefined i vs ocs [cs] = Cinstance (CQType ctx (TAp (cTCon idUndefined) ty)) [undef]
  where ctx   = [ CPred (CTypeclass idUndefined) [getRes (cis_arg_type cs)] ]
        ty    = cTApplys (cTCon i) vs
        aty   = tPosition `fn` tInteger `fn` ty
        body  = CCon1 i (getCISName cs) (CApply (CVar idMakeUndefinedNQ) [CVar id_x, CVar id_y])
        undef = CLValueSign (CDef idMakeUndefinedNQ (CQType [] aty) [CClause [CPVar id_x, CPVar id_y] [] body]) []

doDUndefined i vs ocs cs = Cinstance (CQType [] (TAp (cTCon idUndefined) ty)) [undef]
  where ty    = cTApplys (cTCon i) vs
        aty   = tPosition `fn` tInteger `fn` ty
        undef = CLValueSign (CDef idMakeUndefinedNQ (CQType [] aty) [CClause [] [] (CVar idRawUndef)]) []

doDUninitialized :: Id -> [Type] -> COSummands -> CSummands -> CDefn
-- the single-summand case is not already derived for data declarations with no internal type
-- e.g. ActionWorld, so include it below
doDUninitialized i vs ocs cs = Cinstance (CQType [] (TAp (cTCon idClsUninitialized) ty)) [uninit]
  where ty = cTApplys (cTCon i) vs
        uninit = CLValueSign (rawUninitDef ty) []

-- we put it here for consistency even though it is more related to
-- doDBits and/or dSDeepSeqCond
-- we need to do the freeset `isSubsetOf` tvset check here because
-- we need to decide whether to call primSeqCond or primDeepSeqCond
-- we're on thin ice deriving here - GHC does not support deriving for
-- GADTs not expressible in Haskell 98
doDDeepSeqCond :: Id -> [Type] -> COSummands -> CSummands -> CDefn
doDDeepSeqCond i vs ocs cs = Cinstance instance_cqt $
                                [CLValueSign seq_def []]
  where ty = cTApplys (cTCon i) vs
        fn_ty = ty `fn` ty_forallb
        mkCtx t = CPred (CTypeclass idClsDeepSeqCond) [t]
        -- ctx only required if we use PrimDeepSeqCond
        mty t = toMaybe ((S.fromList (tv t)) `S.isSubsetOf` tvset) t
        ctxss = [ maybeToList mctx ++ ps | oc <- ocs,
                                           CQType ps t <- cos_arg_types oc,
                                           let mctx = fmap mkCtx (mty t) ]
        ctxs = concat ctxss
        fn_cqt = CQType [] fn_ty
        instance_cqt = CQType ctxs (TAp (cTCon idClsDeepSeqCond) ty)
        tvset = S.fromList (concatMap tv vs)
        seqSummand cis = CClause [CPCon1 i (getCISName cis) (CPVar id_x)] [] (cVApply f [CVar id_x])
          where freeset = S.fromList (tv (cis_arg_type cis))
                f = if freeset `S.isSubsetOf` tvset
                    then idPrimDeepSeqCond
                    -- there are unresolved type arguments, so treat it like a function
                    -- there are no contexts (see def of CInternalSummand)
                    -- so we don't need to check for them
                    else idPrimSeqCond
        seq_clauses = map seqSummand cs
        seq_def = CDef idPrimDeepSeqCondNQ fn_cqt seq_clauses


-- -------------------------

doSBounded :: Position -> Id -> [Type] -> CFields -> CDefn
doSBounded dpos i vs fs = Cinstance (CQType ctx (TAp (cTCon idBounded) aty)) [maxB, minB]
  where aty = cTApplys (cTCon i) vs
        ctx = map (\ (CField {cf_type = CQType _ t}) -> CPred (CTypeclass idBounded) [t]) fs
        minB = mmDef (idMinBoundNQ dpos) idMinBound
        maxB = mmDef (idMaxBoundNQ dpos) idMaxBound
        mmDef md mv =
            let mfs = [ (cf_name f, CVar mv) | f <- fs ]
                str = CStruct i mfs
            in        CLValueSign (CDef md (CQType [] aty) [CClause [] [] str]) []

doSUndefined :: Id -> [Type] -> CFields -> CDefn
doSUndefined i vs fs = Cinstance (CQType ctx (TAp (cTCon idUndefined) ty)) [undef]
  where tvset  = S.fromList (concatMap tv vs)
        ty    = cTApplys (cTCon i) vs
        aty   = tPosition `fn` tInteger `fn` ty
        ctx   =  nub [ CPred (CTypeclass idUndefined) [getRes t] | CField {cf_type = CQType _ t} <- fs,
                                                      let freeset = S.fromList (tv t),
                                                      -- trace (ppReadable (S.toList tvset)) $
                                                      -- trace (ppReadable (S.toList freeset)) $
                                                      -- trace (show (freeset `S.isSubsetOf` tvset)) $
                                                      freeset `S.isSubsetOf` tvset ]
        str   = CStruct i [ (cf_name f,
                            (CApply do_undef [CVar id_x, CVar id_y])) | f <- fs,
                                                             let t = cf_type f,
                                                             let freeset = S.fromList (tv t),
                                                             let undef_id = if freeset `S.isSubsetOf` tvset
                                                                            then idMakeUndef
                                                                            else idBuildUndef,
                                                             let do_undef = CVar undef_id ]
        str'  = -- prevent infinite instance loop for structure of no fields
                -- (created by IConv insertion of buildUndefined for empty structures)
                if (null fs) then (CApply (CVar idRawUndef) [CVar id_x, CVar id_y]) else str
        undef = --trace ("ctx: " ++ ppReadable ctx) $
                CLValueSign (CDef idMakeUndefinedNQ (CQType [] aty) [CClause [CPVar id_x, CPVar id_y] [] str']) []

doSUninitialized:: Id -> [Type] -> CFields -> CDefn
doSUninitialized i vs fs = Cinstance (CQType ctx (TAp (cTCon idClsUninitialized) ty)) [uninit]
  where tvset  = S.fromList (concatMap tv vs)
        ty    = cTApplys (cTCon i) vs
        aty   = tPosition `fn` tString `fn` ty
        ctx   =  nub [ CPred (CTypeclass idClsUninitialized) [t] | CField {cf_type = CQType _ t} <- fs,
                                                      let freeset = S.fromList (tv t),
                                                      -- trace (ppReadable (S.toList tvset)) $
                                                      -- trace (ppReadable (S.toList freeset)) $
                                                      -- trace (show (freeset `S.isSubsetOf` tvset)) $
                                                      freeset `S.isSubsetOf` tvset ]
        str   = CStruct i [ (cf_name f, body) | f <- fs,
                            let t = cf_type f,
                            let suffix = "." ++ (getIdBaseString (cf_name f)),
                            let pos = getPosition i,
                            let name' = cVApply idPreludePlus [CVar id_y, stringLiteralAt pos suffix],
                            let freeset = S.fromList (tv t),
                            let uninit_id = if freeset `S.isSubsetOf` tvset
                                            then idPrimMakeUninitialized
                                            else idPrimUninitialized,
                            let do_uninit = CVar uninit_id,
                            let body = (CApply do_uninit [CVar id_x, name']) ]
        uninit = --trace ("ctx: " ++ ppReadable ctx) $
                CLValueSign (CDef idMakeUninitializedNQ (CQType [] aty) [CClause [CPVar id_x, CPVar id_y] [] str]) []

doSDeepSeqCond :: Id -> [Type] -> CFields -> CDefn
doSDeepSeqCond i vs fs = Cinstance (CQType ctx (TAp (cTCon idClsDeepSeqCond) ty)) [dseqcond]
  where tvset  = S.fromList (concatMap tv vs)
        {-
        -- XXX this seems to be bogus
        -- grab field contexts that mention any of the struct's type vars
        -- also must be in result of field
        -- XXX - why is this necessary? (ask Lennart?)
        fieldCtxs f = filter grabCtx ps
           where CQType ps t = cf_type f
                 tvResSet = S.fromList (tv (getRes t))
                 tvInSet s p = any (flip S.member s) (tv p)
                 grabCtx p = tvInSet tvset p && tvInSet tvResSet p
        extraCtxs = concatMap fieldCtxs fs
        -}
        ty     = cTApplys (cTCon i) vs
        def_ty = ty `fn` ty_forallb
        ctx = nub $ [ CPred (CTypeclass idClsDeepSeqCond) [t] | CField {cf_type = CQType _ t} <- fs,
                                                                let freeset = S.fromList (tv t),
                                                                freeset `S.isSubsetOf` tvset ] {- ++ extraCtxs -}
        body = foldr (\(f,val) e -> cVApply f [val, e]) (CVar id_y) blobs
        blobs = [(seqcond_id, field_val)
                     | f <- fs,
                       let cqt@(CQType ps _) = cf_type f,
                       -- drop application if there are contexts
                       -- since we don't seem to handle them correctly
                       null ps,
                       let freeset = S.fromList (tv cqt),
                       let seqcond_id = if freeset `S.isSubsetOf` tvset
                                        then idPrimDeepSeqCond
                                        else idPrimSeqCond,
                       let field_val = CSelectTT i (CVar id_x) (cf_name f)
                ]
        dseqcond = CLValueSign (CDef idPrimDeepSeqCondNQ (CQType [] def_ty) [CClause [CPVar id_x, CPVar id_y] [] body]) []


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
idfshowNQ :: Position -> Id
idfshowNQ pos = setIdPosition pos (unQualId idfshow)
idMaxBoundNQ :: Position -> Id
idMaxBoundNQ pos = setIdPosition pos (unQualId idMaxBound)
idMinBoundNQ :: Position -> Id
idMinBoundNQ pos = setIdPosition pos (unQualId idMinBound)
idMakeUndefinedNQ :: Id
idMakeUndefinedNQ = unQualId idMakeUndef
--idBuildUndefinedNQ = unQualId idBuildUndef
idMakeUninitializedNQ :: Id
idMakeUninitializedNQ = unQualId idPrimMakeUninitialized
--idPrimUninitializedNQ = unQualId idPrimUninitialized
idPrimDeepSeqCondNQ :: Id
idPrimDeepSeqCondNQ = unQualId idPrimDeepSeqCond

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

addRequiredDeriv :: Flags -> SymTab -> Id -> [CType] -> Id -> [CTypeclass]
                 -> [CTypeclass]
addRequiredDeriv flags r i tvs clsId derivs
                         -- incoherent matches are resolved *after* reducePred
    | Right True <- fst (runTI flags False r check) = derivs
  where check = do
          let Just (TypeInfo _ kind _ sort) =
                  {- trace ("check undef: " ++ ppReadable i) $ -}
                  findType r i
          let t = cTApplys (TCon (TyCon i (Just kind) sort)) tvs
          cls <- findCls (CTypeclass clsId)
          vp <- mkVPredFromPred [] (IsIn cls [t])
          -- if there is an existing undefined instance, the predicate will reduce
          mreduce <- reducePred [] Nothing vp
          -- trace (show i ++ ": " ++ ppReadable mreduce) $
          -- trace ("ps' :" ++ ppReadable ps') $
          return (isJust mreduce)

addRequiredDeriv flags r i tvs clsId derivs =
  -- trace ("auto-derive: " ++ ppReadable (cls, i))
  (CTypeclass clsId) : derivs

addRequiredDerivs :: Flags -> SymTab -> Id -> [CType] -> [CTypeclass]
                  -> [CTypeclass]
addRequiredDerivs flags r i tvs derivs =
  foldr (f . setPos) derivs requiredClasses
   where pos    = getIdPosition i
         setPos clsId = setIdPosition pos (unQualId clsId)
         f = addRequiredDeriv flags r i tvs


-- -------------------------
