{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module MakeSymTab(
                  mkSymTab,
                  cConvInst,
                  convCQType, convCQTypeWithAssumps,
                  convCType,
                  ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List
import Control.Monad(when)
import Control.Monad.Except(throwError)
import qualified Data.Set as S
import qualified Data.Map as M

import Data.Either(partitionEithers)
import FStringCompat(concatFString)
import PFPrint
import PreStrings(fsTilde)
import PreIds
import Id
-- for PPrint and PVPrint Id instances
import IdPrint()
import Error(internalError, EMsg, EMsgs(..), ErrMsg(..),
             ErrorHandle, bsError, bsErrorUnsafe)
import CSyntax
import CSyntaxUtil(isEnum)
import SymTab
import CType
import CFreeVars(getFTCDn, getVDefIds, getFTyCons)
import StdPrel
import InferKind(inferKinds)
import Type(fn, tArrow, HasKind(..))
import Pred
import Scheme
import Pragma
import Assump
import Subst
import qualified KIMisc as K
import Data.Maybe
import Unify
import IOUtil(progArgs)
import Util
import SCC(tsort)
import Debug.Trace(traceM)

doTraceKI :: Bool
doTraceKI = "-trace-kind-inference" `elem` progArgs

doTraceOverlap :: Bool
doTraceOverlap = "-trace-instance-overlap" `elem` progArgs

mkSymTab :: ErrorHandle -> CPackage -> IO SymTab
mkSymTab errh (CPackage mi _ imps impsigs _ ds _) =
    let
        mmi = Just mi

        -- ---------------
        -- initial symbol table

        -- the types which are built into the compiler
        -- (not defined in the Prelude etc)
        -- (filtering out numeric and string types is ok because all of the
        -- prelude types have identifiers)
        preTypes' = [(i, ti) | ti@(TypeInfo (Just i) _ _ _ _) <- preTypes]

        -- populate an initial symbol table with the pre-defined items
        -- (note that Prelude classes have recursive access to other classes)
        spre = emptySymtab
                   `addTypesUQ` preTypes'      -- pre-defined types
                   `addVarsUQ` preValues       -- pre-defined values
                   `addClassesUQ` (preClasses symT) -- pre-defined classes

        -- instances from the imported packages
        iinstqs = nub [ (i, qt) | CImpSign _ _ (CSignature _ _ _ ds) <- impsigs,
                                  CIinstance i qt <- ds ]
        qconv qt =
                case convCQType symT qt of
                Left msg -> bsErrorUnsafe errh [msg]
                Right pt -> pt

        cls_fd = -- classes are exported both concretely and abstractly
                 [ (iKName ik, vs, fds) | CImpSign _ _ (CSignature _ _ _ ids) <- impsigs,
                                          Cclass _ _ ik vs fds _ <- ids ] ++
                 [ (iKName ik, vs, fds) | CImpSign _ _ (CSignature _ _ _ ids) <- impsigs,
                                          CIclass _ _ ik vs fds _ <- ids ] ++
                 [ (qualId mi (iKName ik), vs, fds) | Cclass _ _ ik vs fds _ <- ds ]

        -- XXX imported fundeps don't need to be checked
        -- but it is simpler to check them while converting to bss
        fundepErrs = concatMap chkFunDeps cls_fd

        -- instances from this package and from the imports
        -- unsorted because we handle this at the class level
        insts :: QInsts
        insts = [ QInst mi (qconv qt) | Cinstance qt _ <- ds ] ++
                [ QInst mi (qconv qt) | (mi, qt) <- iinstqs ]

        -- a symbol table containing all pre-defined items and all items
        -- from imported packages (except instances and classes)
        -- instances and classes are handled later because of error-handling
        (simp, impClsErrs) = foldl (addImpSyms errh insts) (spre, []) impsigs

        -- all types available to this packaged (predefined and imported)
        preIds = S.fromList (map fst (getAllTypes simp))

        -- ---------------
        -- Errors

        -- the type definitions
        tdefs = filter isTDef ds
        -- the qualified and unqualified names of the types defined here,
        -- plus types already defined
        dids = S.unions (map (getVD mi) tdefs) `S.union` preIds

        -- multiple definitions for the same Id
        dis = filter ((> 1) . length) . group . sort . concatMap getVDefIds $ ds
        -- undefined type references
        uids = S.toList (S.unions (map getFTCDn ds) `S.difference` dids)

        -- check for recursive type synonyms
        type_syn_map = [ (iKName i, S.toList $ getFTyCons t)
                             | (Ctype i _ t) <- tdefs ]
        rec_type_syn_sccs = case (tsort type_syn_map) of
                              Right _ -> []
                              Left sccs -> sccs

        errMultipleDef (i:i':_) =
            let (pos1, pos2) = sortPair (getIdPosition i, getIdPosition i')
            in  (pos2, EMultipleDecl (pfpString i) pos1)
        errMultipleDef is =
            internalError ("MakeSymTab.mkSymTab.errMultipleDef: " ++ show is)
        errUnboundTyCon i = (getIdPosition i, EUnboundTyCon (pfpString i))
        errRecTypeSyn :: [Id] -> EMsg
        errRecTypeSyn scc = (getPosition scc,
                             ETypeSynRecursive (map pfpString scc))

        -- ---------------
        -- Build the symbol table

        -- kind inference
        miks = inferKinds mi simp ds
        iks = case miks of
                  Left msg -> bsErrorUnsafe errh [msg]
                  Right iks -> tracep doTraceKI ("iks: " ++ ppReadable iks) $ iks

        mkQuals = mkDefaultQuals -- always unqualify

        -- previous symbol table with types and classes added
        (symT, clsErrs) = mkTypeSyms errh mkQuals mmi Nothing iks ds insts simp

        allClsErrs = impClsErrs ++ clsErrs

        -- finally, add constructors, fields, and variables
        -- XXX and something about top vars?
        -- XXX and something about instances?
        final_symT =
            let s1 = symAddCons mkQuals mmi Nothing symT ds
                s2 = symAddFields mkQuals mmi Nothing s1 ds
                s3 = symAddVars mkQuals mmi Nothing s2 ds
            in  case (getTopVars s3 mmi Nothing ds) of
                    Left msgs -> bsError errh (errmsgs msgs)
                    Right vs  ->
                        let ivs = [ let i = mkInstId mi (updTypes s3 t)
                                        a = i :>: mustConvCQType s3 [] qt
                                    in  (i, VarInfo VarDefn a Nothing Nothing)
                                  | (mi, qt@(CQType _ t)) <- iinstqs ]
                        in  return $ s3 `addVarsUQ` vs `addVarsUQ` ivs

        -- ---------------
    in
        --trace (ppReadable (S.toList dids)) $
        -- XXX consider reporting multiple error groups at the same time
        if not (null dis) then
            bsError errh (map errMultipleDef dis)
        else if not (null uids) then
            bsError errh (map errUnboundTyCon uids)
        else if not (null rec_type_syn_sccs) then
            bsError errh (map errRecTypeSyn rec_type_syn_sccs)
        else if not (null fundepErrs) then
            bsError errh fundepErrs
        else if not (null allClsErrs) then
            bsError errh allClsErrs
        else
            -- report the kind inference error safely
            case miks of
                Left msg -> bsError errh [msg]
                Right iks -> final_symT


updTypes :: SymTab -> Type -> Type
updTypes r (TCon (TyCon i _ _)) =
    case findType r i of
    Just (TypeInfo (Just i') k _ ti _) -> TCon (TyCon i' (Just k) ti)
    Just (TypeInfo Nothing k _ ti _) ->
        internalError ("updTypes: unexpected numeric or string type:" ++ ppReadable i)
    Nothing -> internalError ("updTypes " ++ ppReadable i)
updTypes r (TAp f a) = TAp (updTypes r f) (updTypes r a)
updTypes r t = t


data QInst = QInst Id (Qual CType)

-- QInsts are directly associated with the instances they name
-- via mkInstId (modulo duplicate instance errors)
instance Eq QInst where
  (QInst mi1 (_ :=> t1)) == (QInst mi2 (_ :=> t2)) =
      mkInstId mi1 t1 == mkInstId mi2 t2

instance Ord QInst where
  compare (QInst mi1 (_ :=> t1)) (QInst mi2 (_ :=> t2)) =
      compare (mkInstId mi1 t1) (mkInstId mi2 t2)

type QInsts = [QInst]

instance PPrint QInst where
  pPrint d p (QInst i qt) = text "(QInst" <+> pPrint d p i <+> pPrint d p qt <> text ")"

instance Show QInst where
  show qi = ppReadable qi

-- typeclass instance head partial order
-- to handle overlapping instances
-- Left LT means ts1 strictly more specific than ts2
-- (should come earlier in instance list)
-- Left EQ means ts1 == ts2
-- (modulo alpha renaming and the like)
-- (i.e. duplicate instance error if not ordered on other fundeps)
-- Left GT means ts2 strictly less specific than ts1
-- (should come later in the instance list)
-- Right False means no overlap
-- (no contribution to partial order)
-- Right True means bad overlap
-- (report an error)
orderInstHead :: [Type] -> [Type] -> Either Ordering Bool
orderInstHead ts1 ts2 =
  case (mu1, mu2) of
    (Nothing, Nothing) -> Right False
    -- ts1 substitution instance of ts2 only
    (Nothing, Just _) -> Left GT
    -- ts2 substitution instance of ts1 only
    (Just _, Nothing) -> Left LT
    (Just s1, Just s2) ->
        case (okSubst vs1 s1, okSubst vs2 s2) of
          (True, True)   -> Left EQ
          (False, True)  -> Left GT
          (True, False)  -> Left LT
          (False, False) -> Right True
  where vs1 = tv ts1
        vs2 = tv ts2
        mu1 = mgu vs1 ts1 ts2
        mu2 = mgu vs2 ts2 ts1
        okSubst vs (s,eqs) = not (any (flip elem $ vs) (getSubstDomain s)) && null eqs

cmpQInsts :: [[Bool]] -> QInst -> QInst -> Either EMsg (Maybe Ordering)
cmpQInsts bss q1@(QInst _ (_ :=> t1)) q2@(QInst _ (_ :=> t2)) = do

  let t1' = expandSyn t1
  let t1_vs = tv t1'

  let t2' = expandSyn t2
  let t2_vs = tv t2'

  let (Forall t1_ks (_ :=> sc1)) = quantify t1_vs ([] :=> t1')
  let (Forall t2_ks (_ :=> sc2)) = quantify t2_vs ([] :=> t2')

  -- replace all the tvs to avoid accidental tv overlap
  -- don't use tmpTyVarIds since they might be in t1_vs or t2_vs
  let tvs = zipWith tVarKind tmpVarIds (t1_ks ++ t2_ks)
  let t1_vs'' = take (length t1_vs) tvs
  let t2_vs'' = take (length t2_vs) (drop (length t1_vs) tvs)

  let t1'' = inst (map TVar t1_vs'') sc1
  let t2'' = inst (map TVar t2_vs'') sc2

  case (splitTAp t1'', splitTAp t2'') of
    ((TCon (TyCon cls1 _ _), ts1),
     (TCon (TyCon cls2 _ _), ts2))| cls1 == cls2 -> do
      when (length ts1 /= length ts2) $
        internalError ("inconsistent class instances: " ++
                       ppReadable ((t1, t1', cls1, ts1), (t2, t2', cls2, ts2)))
      let fd_heads ts = map (flip boolCompress $ ts) (map (map not) bss)
          orders = zipWith orderInstHead (fd_heads ts1) (fd_heads ts2)
          instsPP = ppReadable ((t1, t1', t1''), (t2, t2', t2''))
          succ ord = do
            when doTraceOverlap $
              traceM("inst overlap ok (" ++ show ord ++ "): " ++ instsPP)
            Right $ Just ord
          fail err = do
            when doTraceOverlap $
              traceM ("inst overlap bad: " ++ instsPP)
            Left err
      case (partitionEithers orders) of
        (ords, []) | any (== LT) ords && not (any (== GT) ords) -> succ LT
                   | any (== GT) ords && not (any (== LT) ords) -> succ GT
                   -- XXX duplicate instance error vs overlap error?
                   | all (== EQ) ords -> fail (mkDuplicateError q1 q2)
                   | otherwise -> fail (mkOverlapError q1 q2)
        ([], bads) | or bads -> fail (mkOverlapError q1 q2)
                   | otherwise -> return Nothing
        -- XXX unify with some fundeps but not others?
        otherwise -> fail (mkOverlapError q1 q2)
       -- different classes, so error (we sort on class level now)
    _ -> internalError ("cmpQInsts (different classes): " ++ ppReadable (q1, q2))


-- equally specific instance heads are the same after alpha-renaming
mkDuplicateError :: QInst -> QInst -> EMsg
mkDuplicateError q1@(QInst _ (_ :=> t1)) q2@(QInst _ (_ :=> t2)) =
  (getPosition t2, EDuplicateInstance (pfpReadable t1) (getPosition t1))


-- bad overlapping instances (i.e. cannot be ordered)
mkOverlapError :: QInst -> QInst -> EMsg
mkOverlapError q1@(QInst _ (_ :=> t1)) q2@(QInst _ (_ :=> t2)) =
  (getPosition t1, EBadInstanceOverlap (pfpReadable t1) (pfpReadable t2) (getPosition t2))

chkFunDeps :: (Id, [Id], CFunDeps) -> [EMsg]
chkFunDeps (cls, vs, fds) =
  let
      -- since we want to report several fds in one error message,
      -- return a tuple:  (not full, overlap, extra vars, empty)
      chkOne fd@(as0, bs0) =
          let -- XXX warn if one side has duplicates?
              as = nub as0
              bs = nub bs0
              fd_vars = as ++ bs
              missing = any (\v -> v `notElem` fd_vars) vs
              overlap = as `intersect` bs
              extra = filter (\v -> v `notElem` vs) fd_vars
              empty = (null as) || (null bs)
          in  (fd, (missing, overlap, extra, empty))

      chks = map chkOne fds

      cls_pos = getPosition cls
      cls_str = pfpString (unQualId cls)
      v_strs = map pfpString vs

      notfull_errs =
        let notfull_fds = [ fd | (fd, (True, _, _, _)) <- chks ]
            notfull_fd_strs = mapFst (map pfpString) $
                                 mapSnd (map pfpString) notfull_fds
        in  if (null notfull_fds)
            then []
            else [(cls_pos,
                   EClassFundepsNotFull cls_str v_strs notfull_fd_strs)]

      overlap_errs =
        let overlap_fds = [ (fd, badvs) | (fd, (_, badvs, _, _)) <- chks
                                        , not (null badvs) ]
        in  if (null overlap_fds)
            then []
            else [(cls_pos, EClassFundepsOverlap cls_str)]

      extra_errs =
        let extra_vs = nub $ concat [ badvs | (_, (_, _, badvs, _)) <- chks ]
            extra_v_strs = map pfpString extra_vs
        in  if (null extra_vs)
            then []
            else [(cls_pos, EClassFundepsExtra cls_str extra_v_strs)]

      empty_errs =
        let empty_fds = [ fd | (fd, (_, _, _, True)) <- chks ]
        in  if (null empty_fds)
            then []
            else [(cls_pos, EClassFundepsEmpty cls_str)]
  in
      notfull_errs ++ overlap_errs ++ extra_errs ++ empty_errs

symAddCons :: (Id -> [Id]) -> Maybe Id -> Maybe Id -> SymTab -> [CDefn] -> SymTab
symAddCons mkQuals mi src_pkg s ds =
    addCons mkQuals s $ concatMap (getCons mi src_pkg s) ds

symAddFields :: (Id -> [Id]) -> Maybe Id -> Maybe Id -> SymTab -> [CDefn] -> SymTab
symAddFields mkQuals mi src_pkg s ds =
    addFields mkQuals s
        [(i, FieldInfo si vis n a ifcPragmas def_cs mOrigType src_pkg)
             | (si, n, a@(i :>: _), vis, ifcPragmas, def_cs, mOrigType)
                   <- concatMap (getFields mi s) ds]

symAddVars :: (Id -> [Id]) -> Maybe Id -> Maybe Id -> SymTab -> [CDefn] -> SymTab
symAddVars mkQuals mi src_pkg s ds =
    addVars mkQuals s [(i, VarInfo VarMeth a Nothing src_pkg)
                        | a@(i :>: _) <- concatMap (getMethods mi s) ds]

cConvInst :: ErrorHandle -> SymTab -> CPackage -> CPackage
cConvInst errh r (CPackage mi exps imps impsigs fixs ds includes) =
        CPackage mi exps imps impsigs fixs (map (convInst errh mi r) ds) includes

convInst :: ErrorHandle -> Id -> SymTab -> CDefn -> CDefn
convInst errh mi r di@(Cinstance qt@(CQType _ t) ds) =
    let c = fromJustOrErr "convInst: leftCon" (leftCon t)
        cls = mustFindClass r (CTypeclass c)
        instanceArgs = tyConArgs t
        clsMethType i = case schemes of
                         -- relying on the class arguments being the first variables in the scheme
                         [(Forall ks qt)] -> let ks' = drop (length instanceArgs) ks
                                                 extraTypeVars = zipWith cTVarKind tmpVarIds ks'
                                                 ts = instanceArgs ++ extraTypeVars
                                              in
                                                -- drop first argument because it is the dictionary
                                                -- which is not part of the class method type
                                                case (qualTypeToCQType (inst ts qt)) of
                                                  CQType ps (TAp (TAp (TCon arr) a) r) | isTConArrow arr -> CQType ps r
                                                  qt -> internalError("MakeSymTab.clsMethType 4" ++ ppReadable(i,c,qt))
                         [] -> -- either no type has a field by this name
                               -- or some type has a field by this name, just
                               -- not this type
                               bsErrorUnsafe errh
                                 [(getPosition i,
                                   ENotField (pfpReadable c) (pfpReadable i))]
                         _ -> -- this should not occur because there should
                              -- only be one FieldInfo entry for a given type
                              internalError("MakeSymTab.clsMethType: " ++
                                            "multiple FieldInfo entries: " ++
                                            ppReadable (i, c))
          where schemes = case findField r i of
                           Just fs -> [ sc | FieldInfo { fi_id = ty_id ,
                                                         fi_assump = (_ :>: sc) } <- fs,
                                             ty_id `qualEq` c ]
                           Nothing -> -- no type has a field by this name,
                                      -- let clsMethType error about it
                                      []
        altId (CLValue i cs me) = CLValueSign (CDef (mkUId i) (clsMethType i) cs) me
        altId (CLValueSign (CDef i qt cs) me) = CLValueSign (CDef (mkUId i) qt cs) me
        altId _ = internalError "MakeSymTab.convInst altId"
        mkf d = (i, CVar (mkUId i)) where i = getLName d
        sds = {-trace (ppReadable supsi)-} supsi
          where sups = super cls
                -- keep the position of the subclass contexts around
                (s_ids, s_preds) = unzip sups
                s_poss = map getPosition s_ids
                ats = tyConArgs t
                s_preds' = map mkinst s_preds
                -- once the predicates are made, zip them with the positions
                -- to be used for the position of the field in the CStruct
                supsi = map bnd (zip s_poss s_preds')
                vs = csig cls
                mkinst p =
                    -- This definition doesn't work because "quantify" throws
                    -- away elements of vs which are not in the base type
                    --   let mkgen = let Forall _ (_ :=> t) = quantify vs ([] :=> predToType p) in t
                    --   in  inst ats gen
                    let s = mkSubst (zip vs ats)
                    in  apSub s (predToType p)
                bnd (pos, t) =
                        let tc = fromJustOrErr "convInst bnd: leftCon" (leftCon t)
                            ts = tyConArgs t
                            cqt = CQType [CPred (CTypeclass tc) ts] noType
                        in  (setIdPosition pos (unQualId tc),
                             -- XXX Lennart's comment: hacky encoding of dict
                             -- XXX "tiExpr" looks for this construction
                             CHasType (anyExprAt (getPosition di)) cqt)
        body = Cletrec (map altId ds) (CStruct (Just True) c (map mkf ds ++ sds))
    in  (CValueSign (CDef (mkInstId mi t) qt [CClause [] [] body]))
convInst _ _ _ d = d

mkInstId :: Id -> CType -> Id
mkInstId mi t =
--    trace ("mkInstId " ++ ppReadable (mi,t, expandSyn t)) $
    mkQId (getPosition t) (getIdFString mi) (concatFString (intersperse fsTilde (map getIdFStringP (flat (expandSyn t)))))
  where flat (TVar (TyVar i _ _)) = [i]
        flat (TCon (TyCon i _ _)) = [i]
        flat (TCon (TyNum n _)) = [mkNumId n]
        flat (TCon (TyStr s _)) = [mkStrId s]
        flat (TAp t1 t2) = flat t1 ++ flat t2
        flat _ = internalError "MakeSymTab.mkInstId flat"

getCons :: Maybe Id -> Maybe Id -> SymTab -> CDefn -> [(Id, ConInfo)]
getCons mi src_pkg s data_decl@(Cdata { cd_internal_summands = summands }) = concat (zipWith getInfos summands [0..])
  where rt = cTApplys (cTCon i) (map cTVar (cd_type_vars data_decl))
        i = iKName (cd_name data_decl)
        n = genericLength summands
        tagSize = log2 $ maximum (map cis_tag_encoding summands) + 1
        getInfos summand m = map f_aux cns
          where cns = cis_names summand
                -- make one for each constructor name
                cti = ConTagInfo { conNo = m,
                                   numCon = n,
                                   conTag = cis_tag_encoding summand,
                                   tagSize = tagSize
                                 }
                f_aux cn = (assump_id, info)
                  where assump_id = qual mi cn
                        cqt = CQType [] (cis_arg_type summand `fn` rt)
                        sc = mustConvCQType s (cd_type_vars data_decl) cqt
                        info = ConInfo { ci_id = qual mi i,
                                         ci_visible = cd_visible data_decl,
                                         ci_assump = assump_id :>: sc,
                                         ci_taginfo = cti,
                                         ci_pkg = src_pkg
                                       }
getCons _ _ _ _ = []


-- With a declaration
--   struct S as = { f :: forall bs . C => t }
-- the real type should be
--   f :: forall as . S as -> forall bs . C => t
-- we encode this (since CType lackes nested quantifiers) as
--   f :: forall as bs . C => S as -> t
-- Bool in the result is whether struct is visible to the user.
getFields :: Maybe Id -> SymTab -> CDefn ->
             [(Id, Int, Assump, Bool, [IfcPragma], [CClause], Maybe CType)]
getFields mi s (Cstruct vis _ ik vs ifs fieldNames) =
  let
      -- In "getMethods", the class is turned into a new context.
      -- Here, the struct is turned into a new argument:
      at = cTApplys (cTCon i) (map cTVar vs)
      i = iKName ik
      n = genericLength vs

      -- We need a quantify which will reorder the type variables, to put
      -- the struct type variables first (because moveForAll will later
      -- assume they are first and move the struct argument immediately
      -- following them)
      quantifyWithStructArgument ps at t =
          let tvs = tv at `union` tv ps `union` tv t
              ks = map kind tvs
              s  = mkSubst
                     (zipWith (\ v n -> (v, TGen (getPosition v) n)) tvs [0..])
          in  Forall ks (apSub s (ps :=> (at `fn` t)))

      generatorf :: CField ->
                  (Id, Int, Assump, Bool, [IfcPragma], [CClause], Maybe CType)
      generatorf field@(CField { cf_type = CQType ps t }) =
          -- We re-implement "mustConvCQType" on cqt in steps here,
          -- because the cqt could have contexts whose type variables
          -- will be ordered before those of "at" if we just called
          -- "mustConvCQType" as is.
          case (convCQType s (CQType ps (at `fn` t))) of
              Left msg ->
                  internalError ("MakeSymTab.getFields:\n" ++ ppReadable msg)
              Right (ps' :=> TAp (TAp arr at') t') | arr == tArrow ->
                  (qual mi i,
                   n,
                   qual mi (cf_name field) :>:
                   quantifyWithStructArgument ps' at' t',
                   vis,
                   fromMaybe [] (cf_pragmas field),
                   cf_default field,
                   cf_orig_type field
                  )
              qt ->
                  internalError ("MakeSymTab.getFields: " ++
                                 "converted type changed form:\n" ++
                                 ppReadable qt)
  in  -- traces ("getFields: " ++ ppReadable fieldNames ++ "\nn2: " ) $
      map generatorf ifs

getFields mi s (Cclass _ ps ik vs _ ifs) =
        let cls = mustFindClass s i
            i = CTypeclass (iKName ik)
            zfunc :: (CTypeclass,Pred) -> CPred -> CField
            zfunc (f,_) (CPred (CTypeclass c) ts) =
                CField { cf_name = typeclassId f, cf_pragmas = Nothing,
                         cf_type = CQType [] (cTApplys (cTCon c) ts),
                         cf_default = [],
                         cf_orig_type = Nothing }
            sifs = zipWith zfunc (super cls) ps
        in  getFields mi s (Cstruct True SClass ik vs (ifs ++ sifs) [])

getFields _ _ _ = []



-- For a method of a class, this first produces the type signature with
-- a new first context for the typeclass of which the method is a member:
--     CQType (CPred i (map cTVar vs):ps) t
-- And then it uses mustConvCQType to convert that into a type which
-- first takes in all the type variables (and those of the typeclass
-- will be first) and then takes in the dictionaries for each context.
getMethods :: Maybe Id -> SymTab -> CDefn -> [Assump]
getMethods mi s (Cclass _ _ ik vs _ ifs) =
        let f (CField { cf_name = fi, cf_type = CQType ps t }) =
                qual mi fi :>:
                     mustConvCQType s vs (CQType (CPred (CTypeclass i) (map cTVar vs):ps) t)
            i = iKName ik
        in  map f ifs
getMethods _ _ _ = []

getTopVars :: SymTab -> Maybe Id -> Maybe Id -> [CDefn] -> Either EMsgs [(Id, VarInfo)]
getTopVars r mi src_pkg ds = do
    -- if we want to deprecate top-level types, then this would need to
    -- be lifted out of this function and into "mkSymTab" and "addImpSyms"
    let isDeprecated = makeDeprecatedLookup ds
    let (errs, ass) = partitionEithers $ map (chkTopDef r mi src_pkg isDeprecated) ds
    if null errs then
      return (concat ass)
     else
      throwError (EMsgs errs)

chkTopDef :: SymTab -> Maybe Id -> Maybe Id -> (Id -> Maybe String) -> CDefn -> Either EMsg [(Id, VarInfo)]
chkTopDef r mi src_pkg isDep (Cprimitive i ct) = do
    sc <- mkSchemeWithSymTab r ct
    let i' = qual mi i
    return [(i', VarInfo VarPrim (i' :>: sc) (isDep i) src_pkg)]
chkTopDef r mi src_pkg isDep (CIValueSign i ct) = do
    sc <- mkSchemeWithSymTab r ct
    return [(i, VarInfo VarDefn (i :>: sc) (isDep i) src_pkg)]
chkTopDef r mi src_pkg isDep (Cforeign i qt on ops) = do
    sc@(Forall _ (_ :=> t)) <- mkSchemeWithSymTab r qt
    let name = case on of
                Just s -> s
                Nothing -> getIdString i
        -- We accept functions whose arguments are bits/string and whose
        -- return result is either bits/string or is a
        -- primitive action/actionvalue
        isGoodResult :: CType -> Bool
        isGoodResult t = (isTypeBit t) || (isTypeString t) ||
                         (isTypeActionValue_ t) || (isTypePrimAction t)

        isGoodArg :: CType -> Bool
        isGoodArg t = (isTypeBit t) || (isTypeString t)

        isGoodType :: CType -> Bool
        isGoodType t = let (args, res) = getArrows t
                       in  (all isGoodArg args) && (isGoodResult res)

    let i' = qual mi i
    if isGoodType (expandSyn t) then
        return [(i', VarInfo (VarForg name ops) (i' :>: sc) (isDep i) src_pkg)]
     else
        throwError (getPosition i, EForeignNotBit (pfpString i) (pfpString t))
chkTopDef r mi src_pkg isDep (CValueSign (CDef v t _)) = do
            sc <- mkSchemeWithSymTab r t
            let v' = qual mi v
            return [(v', VarInfo VarDefn (v' :>: sc) (isDep v) src_pkg)]
chkTopDef r mi src_pkg isDep (CValueSign d@(CDefT {})) =
            -- we know that typechecking has not happened yet
            internalError ("getTopVars: " ++ ppReadable d)
chkTopDef _ _ _ _ _ = return []

mkSchemeWithSymTab :: SymTab -> CQType -> Either EMsg Scheme
mkSchemeWithSymTab s cqt =
   case convCQType s cqt of
      Left emsg -> Left emsg
      Right qt -> Right (quantify (tv qt) qt)

mustConvCQType :: SymTab -> [Id] -> CQType -> Scheme
mustConvCQType r _ qt =
    case convCQType r qt of
    Right t ->  quantify (tv t) t
    Left msg -> internalError ("mustConvCQType:\n" ++ ppReadable msg)

mkTypeSyms :: ErrorHandle
           -> (Id -> [Id]) -> Maybe Id -> Maybe Id -> M.Map Id Kind -> [CDefn] -> QInsts
           -> SymTab -> (SymTab, [EMsg])
mkTypeSyms errh mkQuals maybePackageName src_pkg iks defs qts s =
    let importedTypeInfos = concatMap (getTI errh maybePackageName src_pkg r iks) defs
        (cls, errss) =
            unzip $
              [ getCls errh maybePackageName src_pkg iks r incoh ps ik vs fds ifs qts
                    | Cclass  incoh ps ik vs fds ifs <- defs ] ++
              [ getCls errh maybePackageName src_pkg iks r incoh ps ik vs fds []  qts
                    | CIclass incoh ps ik vs fds _   <- defs ]
        r = addClasses mkQuals (addTypes mkQuals s importedTypeInfos) cls
    in  (r, concat errss)

getTI :: ErrorHandle -> Maybe Id -> Maybe Id -> SymTab -> M.Map Id Kind -> CDefn -> [(Id, TypeInfo)]
getTI errh mi src_pkg r iks (Ctype ik vs ct) = [(i, TypeInfo (Just i) k vs (TItype n ct') src_pkg)]
  where i = qual mi (iKName ik)
        k = getK iks ik
        n = genericLength vs
        ks = getNK n k
        ct' = case convCTypeAssumps r (zip vs ks) ct of
              Left msg -> bsErrorUnsafe errh [msg]
              Right t -> apSub (mkSubst (zip (zipWith tVarKind vs ks) (zipWith TGen (map getPosition vs) [0..]))) t
getTI _ mi src_pkg _ iks data_decl@(Cdata {}) =
    -- use getCISName so TIdata only contains the primary constructor names
    [(i, TypeInfo (Just i) k vs ti src_pkg)]
  where i = qual mi (iKName (cd_name data_decl))
        k = getK iks (cd_name data_decl)
        vs = cd_type_vars data_decl
        ti = TIdata { tidata_cons = (map getCISName (cd_internal_summands data_decl))
                    , tidata_enum = (isEnum (cd_original_summands data_decl))
                    }
getTI _ mi src_pkg _ iks (Cstruct _ ss ik vs fs _) =
    [(i, TypeInfo (Just i) (getK iks ik) vs (TIstruct ss (map cf_name fs)) src_pkg)]
  where i = qual mi (iKName ik)
getTI _ mi src_pkg _ iks (Cclass _ ps ik vs _ fs) =
    [(i, TypeInfo (Just i) k vs ti src_pkg)]
  where i = qual mi (iKName ik)
        k = getK iks ik
        ti = TIstruct SClass
                 (map cf_name fs ++
                  map (\ (CPred (CTypeclass i) _) -> i) ps) -- XXX super
getTI _ mi src_pkg _ iks (CItype ik vs _) =
    [(i, TypeInfo (Just i) (getK iks ik) vs TIabstract src_pkg)]
  where i = qual mi (iKName ik)
getTI _ mi src_pkg _ iks (CIclass _ ps ik vs _ _) =
    [(i, TypeInfo (Just i) k vs ti src_pkg)]
  where i = qual mi (iKName ik)
        k = getK iks ik
        ti = TIstruct SClass (map (\ (CPred (CTypeclass i) _) -> i) ps)
getTI _ mi src_pkg _ iks (CprimType ik) =
    [(i, TypeInfo (Just i) (getK iks ik) vs TIabstract src_pkg)]
  where i = qual mi (iKName ik)
        -- the CSyntax doesn't provide type var names
        vs = []
getTI _ _ _ _ _ _ = []

qual :: Maybe Id -> Id -> Id
qual Nothing i = i
qual (Just mi) i = qualId mi i

getK :: M.Map Id Kind -> IdK -> Kind
getK iks ik =
    case M.lookup (iKName ik) iks of
    Just k -> k
    Nothing ->
        case ik of
        IdKind _ k -> k
        _ -> internalError ("getK " ++ ppReadable iks ++ show ik)

getQInsts :: Id -> [[Bool]] -> QInsts -> (QInsts, [EMsg])
-- Exempt classes that are auto-derived for every type from overlap-checking.
-- This limits the impact of the O(n^2) scaling issues because of
-- the O(n^2) instance sort / overlap check. Unfortunately, it
-- isn't an asymptotic fix.
getQInsts ci _ qts
  | ci `elem` autoderivedClasses =
    ([ qi | qi@(QInst _ ( _ :=> t)) <- qts, leftCon t == Just ci ], [])

getQInsts ci bss qts = (cls_qts', errs)
  where cls_qts  = [ qi | qi@(QInst _ ( _ :=> t)) <- qts, leftCon t == Just ci ]
        cls_qt_g = [ (qi, lt_qis) | qi <- cls_qts,
                                    let more_specific qi' = cmpQInsts bss qi' qi == Right (Just LT),
                                    let lt_qis = filter more_specific cls_qts ]
        cls_qts' = case (tsort cls_qt_g) of
                     Left cycles -> internalError ("getQInsts cycles? " ++
                                                   ppReadable (cycles, cls_qt_g))
                     Right sorted -> sorted
        -- XXX another O(n^2) traversal complicated by duplicate instance checking
        chk_pairs = uniquePairs cls_qts
        errs = fst $ partitionEithers $ map (uncurry (cmpQInsts bss)) chk_pairs

doInst :: Maybe Id -> SymTab -> Class -> QInst -> Inst
doInst currentPkg r c (QInst mi p@(ps :=> t)) =
        let args (TAp f a) = args f ++ [a]
            args _ = []
            vs = tv p
            i = setIdPosition (getPosition t) $ mkInstId mi t
            r = CTApply (CVar i) (map TVar vs)
            -- If the instance is from the current package, use Nothing
            -- Otherwise use Just mi to track the source package
            pkg_src = if Just mi == currentPkg then Nothing else Just mi
        in  mkInst r (ps :=> IsIn c (args t)) pkg_src

-- The list bss is used for determining whether a predicate is
-- satisfied by some instance, by matching against the False
-- entries and then unifying with the True entries.  Thus, a
-- list of all False is needed when there are no fundeps.
genBss :: [Id] -> CFunDeps -> [[Bool]]
genBss vs []  = [ replicate (length vs) False ]
genBss vs fds = [ map (`elem` rs) vs | (_, rs) <- fds ]

getCls :: ErrorHandle -> Maybe Id -> Maybe Id -> M.Map Id Kind -> SymTab ->
          -- class components
          Maybe Bool -> [CPred] -> IdK -> [Id] -> CFunDeps -> CFields ->
          QInsts -> (Class, [EMsg])
getCls errh mi src_pkg iks r incoh ps ik vs fds ifs qts =
    let k = getK iks ik
        i = iKName ik
        ks = getNK (genericLength vs) k
        tvs = zipWith tVarKind vs ks
        conv ct = case convCTypeAssumps r (zip vs ks) ct of
                  Left msg -> bsErrorUnsafe errh [msg]
                  Right t -> t
        bss = genBss vs fds
        mkFunDep2 as bs v = if (elem v as) then (Just False)
                            else if (elem v bs) then (Just True)
                            else Nothing
        -- XXX this isn't really meaningful now that fundeps must be full
        -- XXX only being retained in case we change our mind
        -- The list bss2 is used to propagate fundeps for predicates
        -- which are not yet satisfied by an instance.  In this case,
        -- a list of all False leads to useless work.
        bss2 = [ map (mkFunDep2 rs1 rs2) vs | (rs1, rs2) <- fds ]
        qi = qual mi i
        (qinsts, errs) = getQInsts qi bss qts
        c = Class {
         name = CTypeclass qi,
         csig = tvs,
         super = [ (c, IsIn (mustFindClass r c) (map conv ts)) | CPred c ts <- ps ],
         genInsts = \ _ _ _ -> map (doInst mi r c) qinsts,
         tyConOf = TyCon qi (Just k)
                   (TIstruct SClass (map cf_name ifs ++
                                     map (\ (CPred (CTypeclass i) _) -> i) ps)),
         funDeps = bss,
         funDeps2 = bss2,
         allowIncoherent = incoh,
         isComm = False,
         pkg_src = src_pkg
         }
    in  (c, errs)

-- ---------------

trCType :: SymTab -> [(Id, Kind)] -> CType -> K.KI (Type, Kind)
trCType r as ct = do
        --trace ("trCType " ++ ppReadable ct) $
        (t', k) <- trCType' r as ct
        chkTAp t'
        return (t', k)

{- Unused:
isTypish :: TISort -> Bool
isTypish (TIstruct SClass _) = False
isTypish _ = True
-}

trCType' :: SymTab -> [(Id, Kind)] -> CType -> K.KI (Type, Kind)
trCType' r as (TVar (TyVar i n _)) =
    case lookup i as of
    Just k -> return $ (TVar (TyVar i n k), k)
    Nothing -> --trace ("trCTypeN "++ ppReadable(i,as)) $
        K.err (getPosition i, EUnboundTyVar (pfpString i))

trCType' r as t@(TCon (TyNum _ _)) = return (t, KNum)
trCType' r as t@(TCon (TyStr _ _)) = return (t, KStr)
trCType' r as (TCon (TyCon i _ _)) =
    let pos = getPosition i in
    case findType r i of
    -- Disable check if it really is a type for now (was | isTypish ti).
    Just (TypeInfo (Just i') k _ ti _) -> return $ (TCon (TyCon (setIdPosition pos i') (Just k) ti), k)
    Just (TypeInfo Nothing k _ ti _) ->
        internalError("trCTypeN: unexpected numeric type: " ++ ppReadable i)
    _ -> K.err (pos, EUnboundTyCon (pfpString i))
trCType' r as ct@(TAp f a) = do
    (f', fk) <- trCType' r as f
    (a', ak) <- trCType' r as a
    v <- K.unifyFunc f fk a ak
    let t' = TAp f' a'
    return $ (t', v)
trCType' _ _ t@(TGen _ _) = return (t, KStar)
trCType' _ _ t@(TDefMonad _) = internalError "trCTypeN: TDefMonad"

-- Check type synonym applications in the input type.
-- The tricky thing is that we have to expand synonyms before checking
-- to implement LiberalTypeSynonyms correctly.
chkTAp :: Type -> K.KI ()
chkTAp = uncurry (chkTAp' [])  . splitTAp
  where -- f and as should be the outputs of splitTAp, so there should be no remaining TAps
        chkTAp' _ f@(TAp _ _) as = internalError $ "chkTAp' unexpected TAp: " ++ ppReadable (f, as)
        chkTAp' syns (TCon (TyCon i _ (TItype n t))) as
          | i `elem` syns = K.err (getPosition syns, ETypeSynRecursive (map pfpString syns))
          | let numArgs = genericLength as,
            numArgs < n = K.err (getPosition i, EPartialTypeApp (pfpString i) n numArgs)
          | otherwise = let (as1, as2) = genericSplitAt n as
                            t' = setTypePosition (getIdPosition i) t
                            (f', as') = splitTAp $ inst as1 t'
                        in chkTAp' (i:syns) f' (as' ++ as2)
        chkTAp' _ f as = do
          -- f does not contain a TAp or a synonym TCon, so there is nothing to check there,
          -- but the arguments are unchecked.
          _ <- mapM chkTAp as
          return ()

-- -----

convCQType :: SymTab -> CQType -> Either EMsg (Qual Type)
convCQType r ct =
        --trace ("convCQType " ++ ppReadable ct) $
        convCQTypeVars r (tv ct) ct

convCQTypeWithAssumps :: SymTab -> [(Id, Kind)] -> CQType ->
                         Either EMsg (Qual Type)
convCQTypeWithAssumps r as ct =
    let tvs = tv ct
        adjKind tv@(TyVar i n k) = case (lookup i as) of
                                     Nothing -> tv
                                     Just k' -> TyVar i n k'
        tvs' = map adjKind tvs
    in  convCQTypeVars r tvs' ct

convCQTypeVars :: SymTab -> [TyVar] -> CQType -> Either EMsg (Qual Type)
convCQTypeVars r tvs (CQType ps ct) = K.run $ do
    as <- mkTyVarAssumps tvs
    -- convert the preds, first
    -- (this way, we collect the kind info from the preds first)
    let trPred :: CPred -> K.KI (Class, [Type])
        trPred (CPred c ts) = do
            -- Lookup the kinds of the predicate's arguments
            c' <- findClass r c
            let ks = map kind (csig c')
            when (length ks /= length ts) $
                K.err (getPosition c, EKindArg (pfpString $ typeclassId c))
            -- given an argument and it's expected type, convert the type
            -- (unifying the inferred type with the expected type)
            let trPredArg (t, k_expected) = do
                    (t', k_inferred) <- trCType r as t
                    K.unifyType t k_inferred k_expected
                    return t'
            ts' <- mapM trPredArg (zip ts ks)
            return (c', ts')
    ps' <- mapM trPred ps
    -- now convert the base type, unifying with Star
    -- (reporting any kind errors, with what we now know from the preds)
    (ct', k) <- trCType r as ct
    K.unifyType ct k KStar
    -- now put it all together
    s <- K.getKSubst
    let ps'' = map (\ (c, ts) -> IsIn c (map (groundT s) ts)) ps'
--    trace ("conv: " ++ show (vs, ground s t)) $ return ()
    return (map (mkPredWithPositions []) ps'' :=> groundT s ct')

-- -----

convCType :: SymTab -> CType -> Either EMsg Type
convCType r ct = convCTypeVars r (tv ct) ct

convCTypeVars :: SymTab -> [TyVar] -> CType -> Either EMsg Type
convCTypeVars r tvs ct = K.run $ do
    as <- mkTyVarAssumps tvs
    (ct', _) <- trCType r as ct
    return ct'

convCTypeAssumps :: SymTab -> [(Id, Kind)] -> CType -> Either EMsg Type
convCTypeAssumps r as ct = K.run $ do
    (ct', _) <- trCType r as ct
    return ct'

-- -----

mkTyVarAssumps :: [TyVar] -> K.KI [(Id, Kind)]
mkTyVarAssumps tvs = do
    let (nokind_tvs, kind_tvs) = partition (isKVar . kind) tvs
    let known_kinds = [ (getTyVarId tv, kind tv) | tv <- kind_tvs ]
    new_as <- mapM (\ tv -> do v <- K.newKVar (Just (getTyVarId tv)); return (getTyVarId tv, v) )
                   nokind_tvs
    let as = known_kinds ++ new_as
    return as

-- ---------------

findClass :: SymTab -> CTypeclass -> K.KI Class
findClass r i = do
    case findSClass r i of
     Just cl -> return cl
     Nothing -> K.err (getPosition i, EUnboundClCon (pfpString $ typeclassId i))

-- Turn free kind variables into *
groundT :: K.KSubst -> Type -> Type
groundT s (TVar (TyVar i n k)) = TVar (TyVar i n (K.groundK (K.apKSu s k)))
groundT s c@(TCon _) = c
groundT s (TAp l r) = TAp (groundT s l) (groundT s r)
groundT _ _ = internalError "MakeSymTab.groundT"

-----

addImpSyms :: ErrorHandle ->
              QInsts -> (SymTab, [EMsg]) -> CImportedSignature -> (SymTab, [EMsg])
addImpSyms errh insts (s, errs0) (CImpSign name qf (CSignature pkgName _ _ ds)) =
--        trace ("DEBUG: addImpSyms: " ++ name ++ "\n") $
        let mi = Nothing
            src_pkg = Just pkgName
            mkQuals name =
                -- if the package is imported qualified,
                -- only use the qualified name
                if qf
                then [name]
                else mkDefaultQuals name
            (s1, errs1) = mkTypeSyms errh mkQuals Nothing src_pkg M.empty ds insts s
            s2 = symAddFields mkQuals mi src_pkg s1 ds
            s3 = symAddVars mkQuals mi src_pkg s2 ds
        in  case (getTopVars s3 mi src_pkg ds) of
            Left msgs -> bsErrorUnsafe errh (errmsgs msgs)
            Right vs  ->
                (symAddCons mkQuals mi src_pkg (addVars mkQuals s3 vs) ds, errs0 ++ errs1)

-----

-- Get defined variables
getVD :: Id -> CDefn -> S.Set Id
getVD mi d = S.fromList (is ++ map (qualId mi) is)
  where is = getVDefIds d

-----

-- XXX could this be done by embedding the pragma in CValueSign,
-- XXX for instance, rather than by having to match a CPragma with
-- XXX its CValueSign?
makeDeprecatedLookup :: [CDefn] -> (Id -> Maybe String)
makeDeprecatedLookup ds i =
    let deps = [(i,s) | CPragma (Pproperties i props) <- ds,
                        PPdeprecate s <- props]
    in  lookup (unQualId i) deps

-----
