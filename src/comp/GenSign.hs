module GenSign(genUserSign, genEverythingSign) where
import Data.List((\\), sortBy, unionBy, groupBy, partition)
import Data.Maybe(mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad(when)

import PFPrint

import Util

import PreStrings(fsPrelude)
import Error(internalError, EMsg, WMsg, ErrMsg(..),
             ErrorHandle, bsError, bsWarning)
import Id
import FStringCompat(FString, getFString)
import PreStrings(fsEmpty)
import PreIds(tmpTyVarIds, idPrelude, idPreludeBSV, mk_no)
import Position(noPosition)
import Pragma
import CSyntax
import CFreeVars
import CType(leftTyCon, tyConArgs, isTConArrow, allTyCons)
import Pred(Class(..), predToCPred, expandSyn)
import SymTab
import Assump(Assump(..))
import Position(Position(..))
import TypeCheck(qualifyClassDefaults)

--import Util(traces)
--import Debug.Trace


-- ---------------

-- only exports what the user asked to export
-- (auto-exports everything if the user said nothing)
genUserSign :: ErrorHandle -> SymTab -> CPackage -> IO (CSignature, S.Set Id)
genUserSign errh symtab cpkg@(CPackage pkgName _ _ _ _ _ _) =
    -- XXX should we internal error on any errors or warnings?
    case (genSign errh False symtab cpkg) of
        Left msgs -> bsError errh msgs
        Right (sign, warns, reexportedPkgs) -> do
            when (not $ null warns) $ bsWarning errh warns
            -- Track packages used in two ways:
            -- 1. Items from imported packages that end up in exports (export foo, where foo is from Pkg)
            let usedPkgsFromItems = getPackagesUsedByExports pkgName sign
            -- 2. Explicit package re-exports (export Pkg::*)
            let usedPkgs = S.union usedPkgsFromItems reexportedPkgs
            return (sign, usedPkgs)

-- export everything as visible (for internal use in the evaluator)
-- XXX eventually combine this with the above and just have one CSignature
genEverythingSign :: ErrorHandle -> SymTab -> CPackage -> IO CSignature
genEverythingSign errh symtab cpkg =
    case (genSign errh True symtab cpkg) of
        Left msgs -> internalError ("genEverythingSign")
        Right (sig, _, _) -> return sig


-- XXX not quite baked -- attempt to use generics for signature file i/o
-- genSignFileGeneric :: SymTab -> String -> CPackage -> IO ()
-- genSignFileGeneric symtab fn cpack =
--     case genSign symtab cpack of
--      Left  msgs -> messageExit serror msgs
--      Right sign -> writeFileCatch fn (gshow sign)

-- Returns: Either errors (signature, warnings, packages used by non-empty re-exports)
genSign :: ErrorHandle -> Bool -> SymTab -> CPackage ->
           Either [EMsg] (CSignature, [WMsg], S.Set Id)
genSign errh exportAll symt
        pkg@(CPackage currentPkg exportList imps impsigs fixs ds0 includes) =
    let
        -- in the absence of typeclass defaults that are typechecked,
        -- at least record the scope by qualifying identifiers
        -- XXX see comment in tiOneDef for Cclass
        ds = qualifyClassDefaults errh symt ds0

        -- fsCurrentPkg: the FString name of the package being compiled
        fsCurrentPkg = getIdFString currentPkg

        -- exps = export clauses for specified exports or everything
        (exps0, badExports) =
            let all_exps_this_file = concatMap (defExport fsCurrentPkg) ds
            in  case exportList of
                  -- the user said nothing, so export everything
                  Right [] -> (all_exps_this_file, [])
                  Right excludes ->
                    let (excludes', errs) = qualifyExports True symt excludes
                        excludeSet = S.fromList excludes'
                        notExcluded i = i `S.notMember` excludeSet
                    in if exportAll
                       then (all_exps_this_file, errs)
                       else (filter notExcluded all_exps_this_file, errs)
                  -- the user specified exports, so return them (qualified)
                  -- and include everything in this file if writing .bo file
                  Left exports ->
                      let isSelfExport (CExpPkg p) = (p == currentPkg)
                          isSelfExport _           = False
                          (me, others) = partition isSelfExport exports
                          (qual_exports, errs) = qualifyExports False symt others
                          final_exports =
                              if (exportAll || not(null me))
                              then mergeExports all_exps_this_file qual_exports
                              else qual_exports
                      in  (final_exports, errs)
        (exps, packageErrors, reexportedPkgs) = expandPkgExports symt impsigs exps0

        hasEmptyQual i = (getIdQual i == fsEmpty)

        -- a map containing entries for all (qualified) Ids to be exported,
        -- and indicating whether it was exported with (..)
        em = M.fromList (map mkExp exps)
        -- create the entries, and sanity check the exports
        mkExp e | hasEmptyQual (eName e) =
            internalError ("mkExp: not qualified: " ++ ppReadable (eName e))
        mkExp (CExpVar i) = (i, False)
        mkExp (CExpCon i) = (i, False)
        mkExp (CExpConAll i) = (i, True)
        mkExp (CExpPkg {}) = internalError "non-desugared package export"

        -- look: given an identifier, returns
        --         Nothing     (not exported)
        --         Just True   (exported with (..))
        --         Just False  (exported without (..))
        look i = M.lookup i em

        -- insts: imported typeclass instances
        --        (no longer necessary since we transitively close imports)
        --        (were included in ss below)
        -- insts = nub (getInsts pkg)

        -- ss: the signature file entry for exported defs in this package and
        --     all exported defs from imported packages
        (ss, warnss) = unzip $ concatMap (genDefSign symt look currentPkg) ds ++
                                 [ dw | CImpSign _ _ (CSignature ii _ _ ds) <- impsigs,
                                        d <- ds, dw <- genDefSign symt look ii d ]

        -- list of warnings produced while generating signatures
        -- currently only for orphan instances
        warns = concat warnss

        -- def: the names of the defs in ss (that have names)
        def = S.fromList [ i | (Right i) <- map getName ss ]

        -- ssFVs: pairing of each def in ss with
        --        the type constructors referenced in it
        ssFVs = map (\s -> (s, getFTCDn s)) ss

        -- use: set of the type constructors used in ss
        use = S.unions (map snd ssFVs)

        -- isHiddenDef: whether the constructors of the type def are visible
        isHiddenDef (Cdata { cd_visible =  vis }) = not vis
        isHiddenDef (CIclass _ _ _ _ _ _) = True
        isHiddenDef d = False

        -- useLoci: map from used variable to definitions where it's used
        --          (excepting data defs with non-visible constructors,
        --          and unnamed defs (like pragmas and instances))
        useLoci :: M.Map Id [Id]
        useLoci = M.fromList [ (var, def_names)
                              | var <- S.toList use
                              , let def_names = [ i | (def, fvs) <- ssFVs
                                                    , not (isHiddenDef def)
                                                    , var `S.member` fvs
                                                    , (Right i) <- [getName def] ]
                              , not (null def_names) ]

        -- udef: used but not defined types (and typeclasses)
        --       in the signature-file format (CItype and CIclass),
        --       from this package only
        --       (if it's in another package, the user of this package
        --       can import that other package; if it's in this package,
        --       nothing can be done, so we will error ... see below)
        udef :: [CDefn]
        udef = sortBy cmpName [ td |
                                -- primitives which are available but
                                -- not declared/exported should be ignored
                                -- (idArrow, idAdd, idMax, idLog, idDiv, etc)
                                -- for simplicity, we ignore all prelude
                                -- qualified types
                                fsCurrentPkg /= fsPrelude,
                                i <- S.toList (S.difference use def),
                                -- only consider Ids from this package
                                getIdQFString i == Just fsCurrentPkg,
                                {- not (isTCId i), -} td <- tdef i ]
            where cmpName t1 t2 = case (getName t1, getName t2) of
                                    (Right i1, Right i2) -> cmpIdByName i1 i2
                                    (Right _, Left _) -> GT
                                    (Left _, Right _) -> LT
                                    (Left _, Left _) -> EQ

        -- given a used type constructor, find the type that it belongs to
        -- and return it in signature-file form (CItype or CIclass)
        tdef i = case findType symt i of
                 Just x@(TypeInfo _ k vs (TIstruct SClass _) _) ->
                     case (findSClass symt (CTypeclass i)) of
                       Nothing -> internalError ("GenSign.genSign: " ++
                                                 "couldn't find class " ++
                                                 ppReadable i)
                       Just cl ->
                           -- classToIClass doesn't need "vs" since the Class
                           -- stores the tyvars as well
                           [classToIClass i k cl (findPoss i)]
                 Just ti@(TypeInfo _ k vs (TItype _ _) _) ->
                     --trace ("DEBUG ==> tdef " ++ ppString i ++ "\n" ++
                     --       ppString ti ++ "\n" ++
                     --       ppString (M.lookup i useLoci))
                     [CItype (IdKind i k) (varsk (mkTyVarIds vs) k) (findPoss i)]
                 Just ti@(TypeInfo _ k vs _ _) ->
                     --trace ("DEBUG ==> tdef " ++ ppString i ++ "\n" ++
                     --       ppString ti ++ "\n" ++
                     --       ppString (M.lookup i useLoci))
                     [CItype (IdKind i k) (varsk (mkTyVarIds vs) k) (findPoss i)]
                 Nothing -> internalError "genSign"
            where -- positions of the uses which necessitated exporting this def
                  -- XXX we could get rid of this
                  findPoss i = case (M.lookup i useLoci) of
                                 Just us -> map getIdPosition us
                                 Nothing -> [noPosition]
                                    -- XXX when not "exportAll",
                                    -- XXX some positions are not found
                                    --internalError ("GenSign tdef: " ++
                                    --               pfpString i)
                  -- use any user-given names, then continue with temp names
                  -- but not any that have already been used
                  mkTyVarIds vs = vs ++ (tmpTyVarIds \\ vs)
                  varsk (v:vs) (Kfun _ k) = v : varsk vs k
                  varsk _      _          = []

        -- ss': the def ss extended with type classes (CIclass)
        --      (any types CItype in udef will be reported as an error)
        ss' = ss ++ udef

        -- impids: the imported packages (not including the Preludes)
        impids = filter (\ x -> x /= idPrelude && x /= idPreludeBSV)
                        (map impName imps)

        -- sign: the signature file
        sign = CSignature currentPkg impids fixs ss'

        -- missingExportNames: types (defined in this package) which are
        --     used in exported signatures, but are not themselves exported
        --     (to be reported as an error)
        missingExportNames = ([name | (CItype (IdKind name _) _ _) <- udef] ++
                              [name | (CItype (IdK name ) _ _) <- udef])
        mkETypeNotExported name =
            let unexpName = pfpString (unQualId name)
                err = internalError ("GenSign.genSign.mkTypeNotExported (" ++
                                     pfpString name ++ ")")
                defIds = M.findWithDefault err name useLoci
                defNamesPos = [(pfpString (unQualId name), getIdPosition name)
                                  | name <- defIds]
            in  ETypeNotExported unexpName defNamesPos

        -- missing exports: type errors for identifiers that
        --   - have not been exported
        --   - are defined in this package
        --   - are used in an exported definition (except hidden data defs)
        missingExports =
            [(getIdPosition name, mkETypeNotExported name)
                | name <- missingExportNames,
                  -- has uses which aren't hidden
                  name `M.member` useLoci]

        errors = packageErrors ++ missingExports ++ badExports

        -- sanity check
        failedExports = ([] :: [Id])
         {- -- only needed for debugging
            let ss_names = [ i | (Right i) <- map getName ss ]
                exp_names = map eName exps
            in  -- duplicates are OK because they are qualified
                filter (`notElem` ss_names) exp_names
         -}
    in
{-
        trace ("\nexps=\n" ++ ppReadable exps ++
               "\n\ndefs=\n" ++ ppReadable ds ++
               "\n\nem=\n" ++ ppReadable (M.toList em) ++
               "\n\nss=\n" ++ ppReadable ss ++
               "\n\nudef=\n" ++ ppReadable udef ++
               "\n\nss'=\n" ++ ppReadable ss' ++ "\n\n") $
-}
        case errors of
            [] -> if (not (null failedExports))
                  then internalError ("failed exports: " ++
                                      ppReadable failedExports)
                  else Right (sign, warns, reexportedPkgs)
            errs -> Left errs

-- ---------------

-- get the name of an export
eName :: CExport -> Id
eName (CExpVar i) = i
eName (CExpCon i) = i
eName (CExpConAll i) = i
eName (CExpPkg {}) = internalError "non-desugared package export"

-- ---------------

{- -- Unused
getInsts (CPackage _ _ imps _ pds includes) =
        [ i | CImpSign _ _ (CSignature _ _ _ ds) <- imps, i@(CIinstance _ (CQType _ t)) <- ds,
              not (all (fromPrelude . leftTyCon) (t : tyConArgs t)) ]
-- XXX Might break if a Prelude type was declared outside the Prelude to be an
--        instance of a Prelude typeclass, and an attempt was made to use that
--        instance in a third file.

fromPrelude (Just (TyCon i _ _)) = (getIdQFString i == Just fsPrelude
                                    || getIdQFString i == Just fsPreludeBSV)
fromPrelude _ = True
-}

-- ---------------

-- XXX export from symbol table
-- check export list
genDefSign :: SymTab -> (Id -> Maybe Bool) -> Id -> CDefn -> [(CDefn, [WMsg])]
genDefSign s look currentPkg d@(Ctype ik vs t) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just _ -> [(Ctype (qualIdK currentPkg s ik) vs (qualType s t), [])]
genDefSign s look currentPkg d@(Cdata { cd_visible = vis,
                                        cd_name = ik,
                                        cd_type_vars = vs,
                                        cd_original_summands = ocs,
                                        cd_internal_summands = cs }) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
--    Just False -> [CItype (qualIdK currentPkg s ik) vs]
    Just vis' -> [(Cdata { cd_visible = vis && vis',
                          cd_name = qualIdK currentPkg s ik,
                          cd_type_vars = vs,
                          cd_original_summands = map qual_original_summand ocs,
                          cd_internal_summands = map qual_internal_summand cs,
                          cd_derivings = [] }, [])]
                 where qual_original_summand summand =
                           summand { cos_names = map (qualId currentPkg)
                                                  (cos_names summand) }
                       qual_internal_summand summand =
                           summand { cis_names = map (qualId currentPkg)
                                                  (cis_names summand),
                                     cis_arg_type = (qualType s
                                                     (cis_arg_type summand)) }

genDefSign s look currentPkg d@(Cstruct vis ss@(SDataCon i _) ik vs fs _) =
  let qi = qualId currentPkg i
  in
    case look qi of
    Just True -> [(Cstruct vis ss (qualIdK currentPkg s ik) vs (qualFields currentPkg s fs) [], [])]
    _ -> []
genDefSign s look currentPkg d@(Cstruct vis ss ik vs fs _) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
--    Just False -> [CItype (qualIdK currentPkg s ik) vs]
    Just vis' -> [(Cstruct (vis && vis') ss (qualIdK currentPkg s ik) vs (qualFields currentPkg s fs) [], [])]
genDefSign s look currentPkg (Cclass incoh ps ik vs fds fs) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just True -> [(Cclass incoh (map (qualPred s) ps) (qualIdK currentPkg s ik) vs fds (qualFields currentPkg s fs),[])]
    Just False -> [(CIclass incoh (map (qualPred s) ps) (qualIdK currentPkg s ik) vs fds [getPosition ik], [])]
genDefSign s look currentPkg d@(Cinstance qt@(CQType ps t) _) =
    -- trace (ppReadable (leftCon t, map leftCon (tyConArgs t))) $
    let tcs = leftTyCons (t : tyConArgs t) in
    if all (\c -> exported c || imported c) tcs then
        [(CIinstance currentPkg (qualCQType s qt), [(getPosition d, WOrphanInst (pfpString (expandSyn t))) | orphan_inst ])]
    else
        []
  where leftTyCons = mapMaybe leftTyCon
        addQual i = if (getIdQual i == fsEmpty)
                    then qualId currentPkg i
                    else i
        exported (TyCon _ _ (TIstruct (SDataCon i _) _)) =
            look (addQual i) == Just True
        -- there's a special case since we can't export -> from the Prelude
        exported c@(TyCon i _ _) =
            look (addQual i) /= Nothing ||
                                (isTConArrow c && getIdFString currentPkg == fsPrelude)
        exported (TyStr _ _) = False
        exported (TyNum _ _) = False
        imported (TyCon i _ _) = getIdQual i /= getIdFString currentPkg
        -- TyNum/TyStr are imported for the purposes of the "orphan check"
        imported (TyNum _ _) = True
        imported (TyStr _ _) = True
        fj1 = fromJustOrErr ("bad instance con: " ++ ppReadable qt)
        cls_tcon = fj1 $ leftTyCon t
        cls_con_name = CTypeclass $ fj1 $ leftCon t
        fj2 = fromJustOrErr ("missing instance class: " ++ ppReadable qt)
        cls = fj2 $ findSClass s cls_con_name
        inst_cls_args = map expandSyn (tyConArgs t)
        fd_sigs = map (map not) (funDeps cls)
        inst_heads = zipWith boolCompress fd_sigs (repeat inst_cls_args)
        orphan_head = not . (any exported) . (concatMap allTyCons)
        orphan_inst = imported (cls_tcon) && any orphan_head inst_heads

genDefSign s look currentPkg (CValueSign (CDef i qt _)) =
  let qi = qualId currentPkg i
  in  case look qi of
        Nothing -> []
        Just _ -> [(CIValueSign qi (qualCQType s qt), [])]
genDefSign s look currentPkg (Cforeign i qt ms mps) =
  let qi = qualId currentPkg i
  in  case look qi of
        Nothing -> []
        Just _ -> [(Cforeign qi (qualCQType s qt) ms mps, [])]
genDefSign s look currentPkg (Cprimitive i qt) =
  let qi = qualId currentPkg i
  in  case look qi of
        Nothing -> []
        Just _ -> [(Cprimitive qi (qualCQType s qt), [])]
genDefSign s look currentPkg (CprimType ik) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just _ -> [(CprimType (qualIdK currentPkg s ik), [])]
genDefSign s look currentPkg (CIValueSign i qt) =
  let qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just _ -> [(CIValueSign i qt, [])]
genDefSign s look currentPkg (CItype ik vs poss) =
  let i = iKName ik
      qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just _ -> [(CItype ik vs poss, [])]
genDefSign s look currentPkg (CPragma (Pproperties i props)) =
  let qi = qualId currentPkg i
  in
    case look qi of
    Nothing -> []
    Just _ ->
        -- preserve certain pragmas
        -- (so far, just the "deprecate" pprop)
        let props' = [ p | p@(PPdeprecate _) <- props ]
        in  if (null props')
            then []
            else [(CPragma (Pproperties i props'), [])]
genDefSign s look currentPkg d = []

-- ---------------

qualIdK :: Id -> SymTab -> IdK -> IdK
qualIdK currentPkg s (IdKind i k) = IdKind (qualId currentPkg i) k
qualIdK currentPkg s idk =
    let i = iKName idk
    in  case findType s i of
          Just (TypeInfo (Just i') k _ _ _) -> IdKind i' k
          Nothing -> IdK (qualId currentPkg i)
          Just (TypeInfo Nothing k _ _ _) ->
            internalError ("qualIdK: unexpected numeric type: " ++
                           ppReadable i)

qualCQType :: SymTab -> CQType -> CQType
qualCQType s (CQType ps t) = CQType (map (qualPred s) ps) (qualType s t)

qualPred :: SymTab -> CPred -> CPred
qualPred s (CPred (CTypeclass i) ts) = CPred (CTypeclass (qualTId s i)) (map (qualType s) ts)

qualFields :: Id -> SymTab -> CFields -> CFields
qualFields currentPkg s fs = [f { cf_name = qualId currentPkg (cf_name f),
                                  cf_type = qualCQType s (cf_type f) }
                              | f <- fs ]

qualType :: SymTab -> CType -> CType
qualType s (TCon (TyCon i k si)) = TCon (TyCon (qualTId s i) k si)
qualType s t@(TCon (TyNum _ _)) = t
qualType s t@(TCon (TyStr _ _)) = t
qualType s t@(TVar _) = t
qualType s (TAp t t') = TAp (qualType s t) (qualType s t')
qualType s t@(TGen _ _) = t
qualType s t@(TDefMonad _) = internalError "qualType: TDefMonad"

qualTId :: SymTab -> Id -> Id
qualTId s i =
    case findType s i of
    Just (TypeInfo (Just i') _ _ _ _) -> i'
    Just (TypeInfo Nothing _ _ _ _) ->
        internalError ("qualTId: unexpected numeric type: " ++ ppReadable i)
    Nothing -> i

-- ---------------

-- Given a def, return its (qualified) export if it should be exported
-- (dummies and generated ifc should not).
-- This is mapped over the defs in a package in order to force export of
-- all definitions.
defExport :: FString -> CDefn -> [CExport]
defExport pkgName def =
    case (getName def) of
      Left _ -> []
      Right i ->
          let qual_i = setIdQual i pkgName
          in  if (hasIdProp i IdPGeneratedIfc) then []
              else if (isTDef def)             then [CExpConAll qual_i]
                                               else [CExpVar qual_i]

-- given full expors of everything in this file and a list of explicit
-- exports, union in any explicit exports not from this file.
-- "union" doesn't work, because the user could have exported a local
-- type without its constructors, and we want to throw that out in favor
-- of exporting the type fully.
mergeExports :: [CExport] -> [CExport] -> [CExport]
mergeExports all_exps_this_file user_exps =
    let eq (CExpVar i)    (CExpVar i')    = (i == i')
        eq (CExpConAll i) (CExpCon i')    = (i == i')
        eq (CExpConAll i) (CExpConAll i') = (i == i')
        -- these two should never come up in the "union"
        eq (CExpCon i)    (CExpConAll i') = (i == i')
        eq (CExpPkg i)    (CExpPkg i')    = (i == i')
        eq _              _               = False
    in
        unionBy eq all_exps_this_file user_exps

-- ---------------

qualifyExports :: Bool -> SymTab -> [CExport] -> ([CExport], [EMsg])
qualifyExports exclude symt exps =
    let
        mkUnboundExport i = (getIdPosition i, EUnboundExport (pfpString i) exclude)
        mkDupExport i = (getIdPosition i, EDuplicateExport (pfpString i) exclude)
        mkIdInPkgExport (i, p) =
            (getIdPosition i,
             EDuplicateDefInPackageExport (getFString p) (pfpString i))

        qualifyType c i =
            case (findType symt i) of
              -- if the name was unqualified, now it will be qualified
              Just (TypeInfo (Just i') _ _ _ _) -> Left (c i')
              Nothing -> Right (mkUnboundExport i)
              Just _ -> internalError ("qualifyPkgExports: " ++
                                       "unexpected numeric type: " ++
                                       ppReadable i)

        qualifyVar c i =
            case (findVar symt i) of
              -- if the name was unqualified, now it will be qualified
              Just (VarInfo _ (i' :>: _) _ _) -> Left (c i')
              Nothing -> Right (mkUnboundExport i)

        addId i (Left exp) = Left (i, exp)
        addId _ (Right msg) = Right msg

        -- * Either is used to identify error vs success
        -- * exports are paired with the original Id for better
        --   error messages (position and qualifier)
        qualifyExp e@(CExpVar i) = addId i $ qualifyVar CExpVar i
        qualifyExp e@(CExpCon i) = addId i $ qualifyType CExpCon i
        qualifyExp e@(CExpConAll i) = addId i $ qualifyType CExpConAll i
        -- when package exports are expanded, they will be qualified
        qualifyExp e@(CExpPkg p) = addId p $ Left e

        (qual_exp_pairs, unboundErrs) = separate $ map qualifyExp exps
        qual_exps = map snd qual_exp_pairs

        -- report duplicate identifiers, duplicate packages, and when
        -- an identifier is also covered by a package
        (exp_pkgs, exp_ids) =
            let isPkg (_, CExpPkg p) = Left p
                isPkg (i, e) = Right (i, eName e)
            in  separate (map isPkg qual_exp_pairs)
        duplicate_pkgs =
            concatMap (tailOrErr "duplicate_pkgs") (findSame exp_pkgs)
        -- keep the qualified Ids for filtering id_vs_pkg duplicates
        duplicate_ids =
            let cmpSnd (_,x) (_,y) = x `compare` y
                eqSnd  (_,x) (_,y) = x == y
            in  concatMap (map fst . tailOrErr "duplicate_exps") $
                    findSameBy cmpSnd eqSnd  exp_ids
        duplicate_id_vs_pkg =
            let pkgSet = S.fromList (map getIdBase exp_pkgs)
                isDup (_,i) = S.member (getIdQual i) pkgSet
                qual_dups = filter isDup exp_ids
                -- only report one overlap
                eqSnd  (_,x) (_,y) = x == y
                unique_qual_dup = map (headOrErr "duplicate_id_vs_pkg") $
                                      groupBy eqSnd qual_dups
            in  map (\(i,e) -> (i, getIdQual e)) unique_qual_dup
        duplicateErrs =
            map mkDupExport duplicate_ids ++
            map mkDupExport duplicate_pkgs ++
            map mkIdInPkgExport duplicate_id_vs_pkg
   in
        (qual_exps, unboundErrs ++ duplicateErrs)

-- ---------------

-- replace the re-export of a package with re-export of its contents
-- (we choose to not export those Ids which are shadowed by other defs,
-- so this function takes the symbol table, as a way to check whether
-- the unqualified name refers to the qualified name that we are exporting)
-- Returns: (expanded exports, errors, set of packages with non-empty re-exports)
expandPkgExports :: SymTab -> [CImportedSignature] -> [CExport] -> ([CExport], [EMsg], S.Set Id)
expandPkgExports symt impsigs exps =
    let
        unqualTypeIsThisOne i =
            case (findType symt (unQualId i)) of
              Just (TypeInfo (Just i') _ _ _ _) -> getIdQual i' == getIdQual i
              _ -> False

        unqualVarIsThisOne i =
            case (findVar symt (unQualId i)) of
              Just (VarInfo _ (i' :>: _) _ _) -> getIdQual i' == getIdQual i
              _ -> False

        expandOne :: CExport -> Either ([CExport], Maybe Id) EMsg
        expandOne (CExpPkg pkg) =
            let dss = [ ds | (CImpSign _ _ (CSignature i _ _ ds)) <- impsigs,
                             i == pkg ]
            in  case (dss) of
                    [] -> let pos = getPosition pkg
                          in  Right (pos, EUnboundPackage (pvpString pkg))
                    (ds:_) -> let expanded = mapMaybe pkgExport ds
                                  usedPkg = if null expanded then Nothing else Just pkg
                              in  Left (expanded, usedPkg)
        expandOne e = Left ([e], Nothing)

        -- function to re-export a def
        pkgExport :: CDefn -> Maybe CExport
        pkgExport def =
            case (getName def) of
              -- don't export unnamed defs (instances, pragmas, etc)
              Left _ -> Nothing
              Right i ->
                  let isShadowed =
                          if (isTDef def)
                          then not (unqualTypeIsThisOne i)
                          else not (unqualVarIsThisOne i)
                      isAbstractTDef (CItype {}) = True
                      isAbstractTDef _           = False
                  in
                      -- don't declare shadowed or hidden names
                      -- XXX or do we only want to not declare those shadowed by
                      -- XXX other exports?
                      if isShadowed                then Nothing
                      -- types exported abstractly
                      else if (isAbstractTDef def) then Just $ CExpCon i
                      -- all other types export fully
                      else if (isTDef def)         then Just $ CExpConAll i
                      -- non-types
                                                   else Just $ CExpVar i

        (results, errs) = separate $ map expandOne exps
        (expandedLists, maybePkgs) = unzip results
        usedPkgs = S.fromList $ mapMaybe id maybePkgs
    in
        (concat expandedLists, errs, usedPkgs)

-- ---------------

classToIClass :: Id -> Kind -> Class -> [Position] -> CDefn
classToIClass i k (Class { csig=tvs, super=ps, funDeps2=bss2,
                           allowIncoherent = incoh}) poss =
    let getTVarId (TyVar i _ _) = i
        tvis = map getTVarId tvs

        -- This create CIclass with the user-given names for type vars.
        -- It uses the names from "csig" in the Class, but it could also
        -- have used the Ids from the TypeInfo.

        -- convert (Id,Pred) to CPred
        ps' = map (predToCPred . snd) ps

        -- reconstruct the fundeps from bss2
        bsToFd bs =
            let bis = zip bs tvis
                foldFn (b,i) iss@(is1, is2) =
                    case b of
                        Nothing -> iss
                        Just True  -> (is1, i:is2)
                        Just False -> (i:is1, is2)
            in  foldr foldFn ([],[]) bis
        fds = map bsToFd bss2
    in
        CIclass incoh ps' (IdKind i k) tvis fds poss

-- ---------------
-- Package usage tracking for unused import warnings

-- Extract packages used by exports (for Phase 3 of unused import detection).
-- Only tracks re-exported items (from other packages). Local exports are already
-- tracked during type checking (Phase 2). For re-exports, only record the package
-- of the item itself, not types within its definition.
getPackagesUsedByExports :: Id -> CSignature -> S.Set Id
getPackagesUsedByExports currentPkg (CSignature _ _ _ defns) =
    let allPkgs = mapMaybe getPackageFromDefn defns
        externalPkgs = filter (/= currentPkg) allPkgs
    in  S.fromList externalPkgs
  where
    -- Get the package qualifier from a qualified Id
    getIdPackage :: Id -> Maybe Id
    getIdPackage i =
        let qual = getIdQual i
        in  if qual == fsEmpty
            then Nothing
            else Just (mk_no qual)

    -- Get the package of the item being exported (not types within its definition)
    getPackageFromDefn :: CDefn -> Maybe Id
    getPackageFromDefn (Ctype (IdKind i _) _ _) = getIdPackage i
    getPackageFromDefn (CItype (IdKind i _) _ _) = getIdPackage i
    getPackageFromDefn (Cdata { cd_name = IdKind i _ }) = getIdPackage i
    getPackageFromDefn (Cstruct _ _ (IdKind i _) _ _ _) = getIdPackage i
    getPackageFromDefn (Cclass _ _ (IdKind i _) _ _ _) = getIdPackage i
    getPackageFromDefn (CIclass _ _ (IdKind i _) _ _ _) = getIdPackage i
    getPackageFromDefn (CIValueSign i _) = getIdPackage i
    getPackageFromDefn (Cforeign i _ _ _) = getIdPackage i
    getPackageFromDefn (Cprimitive i _) = getIdPackage i
    getPackageFromDefn (CprimType (IdKind i _)) = getIdPackage i
    getPackageFromDefn (CIinstance _ _) = Nothing  -- Instances don't have a name
    getPackageFromDefn (CPragma _) = Nothing
    getPackageFromDefn d = internalError $ "GenSign.getPackageFromDefn unexpected defn in signature: " ++ ppReadable d
-- ---------------
