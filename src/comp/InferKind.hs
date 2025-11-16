{-# LANGUAGE PatternGuards #-}
module InferKind(inferKinds) where
import Data.List((\\))
import qualified Data.Set as S
import qualified Data.Map as M
import Util(map_insertMany)
import Error(internalError, EMsg, ErrMsg(..))
import Id
import CSyntax
import CFreeVars(getFQTyVars, getCPTyVars)
import SymTab
import KIMisc
import PFPrint

--import Debug.Trace


inferKinds :: Id -> SymTab -> [CDefn] -> Either EMsg (M.Map Id Kind)
inferKinds mi s ds = run $ do
    let get (Ctype ik _ _) = getIK ik
        get (Cdata { cd_name = name }) = getIK name
        get (Cstruct _ _ ik _ _ _) = getIK ik
        get (Cclass _ _ ik _ _ _) = getIK ik
        get (CItype ik _ _) = getIK ik
        get (CIclass _ _ ik _ _ _) = getIK ik
        get (CprimType ik) = getIK ik
        get _ = return []
        getIK (IdK i) = do v <- newKVar (Just i); return [(i, v)]
        getIK (IdKind i k) = return [(i, k)]
        getIK (IdPKind i pk) = do k <- convertPKindToKind pk; return [(i, k)]
    ass <- mapM get ds
    -- assumptions about the types defined in this package
    let as = concat ass
    -- a list of the assumps from this package, those assumps qualified,
    -- and the assumps about types from imported packages (the symtab)
    -- XXX this relies on the order of M.fromList, to bias earlier pairs
    let as' = -- place these first, so that they are shadowed by
              -- any assumps of the same name in "as"
              [(i, k) | (i, TypeInfo _ k _ _ _) <- getAllTypes s ] ++
              as ++
              map (\ (n,v) -> (qualId mi n, v)) as
    let as_map = M.fromList as'
    mapM_ (inferKDefn as_map) ds
    s <- getKSubst
    --trace(ppReadable as') $ return ()
    return (fmap (groundK . apKSu s) as_map)

convertPKindToKind :: PartialKind -> KI Kind
convertPKindToKind (PKNoInfo) = do v <- newKVar Nothing; return v
convertPKindToKind (PKStar) = return KStar
convertPKindToKind (PKNum) = return KNum
convertPKindToKind (PKStr) = return KStr
convertPKindToKind (PKfun l r) = do l' <- convertPKindToKind l
                                    r' <- convertPKindToKind r
                                    return (Kfun l' r')

type Assumps = M.Map Id Kind

makeAssump :: Id -> KI (Id, Kind)
makeAssump i = do v <- newKVar (Just i); return (i, v)

inferKDefn :: Assumps -> CDefn -> KI ()
inferKDefn as (Ctype ik vs ct) = do
    let i = iKName ik
        con_k = mustFindK i as
    (as', mk) <- unifyDefArgs i con_k vs
    ctk <- kcCType (map_insertMany as' as) ct
    unifyDefAlias i con_k as' mk ct ctk
inferKDefn as (Cdata { cd_name = ik,
                       cd_type_vars = vs,
                       cd_internal_summands = cs }) = do
    let i = iKName ik
        con_k = mustFindK i as
    (as', mk) <- unifyDefArgs i con_k vs
    let as'' = map_insertMany as' as
    mapM_ (\ summand -> kcCTypeStar as'' (cis_arg_type summand)) cs
    unifyDefStar i con_k as' mk
inferKDefn as (Cstruct _ _ ik vs fs _) = do
    let i = iKName ik
        con_k = mustFindK i as
    (as', mk) <- unifyDefArgs i con_k vs
    let as'' = map_insertMany as' as
        doField field = do
                let vs' = getFQTyVarsL (cf_type field) \\ vs
                as''' <- mapM makeAssump vs'
                kcCQTypeStar (map_insertMany as''' as'') (cf_type field)
    mapM_ doField fs
    unifyDefStar i con_k as' mk
inferKDefn as (Cclass _ ps ik vs _ fs) = do
    let i = iKName ik
        con_k = mustFindK i as
    (v_as, mk) <- unifyDefArgs i con_k vs
    -- there may be additional variables in the superclass
    -- XXX we should confirm that they are dependent utimately on "vs"
    let pvs = concatMap (S.toList . getCPTyVars) ps \\ vs
    pv_as <- mapM makeAssump pvs
    let as' = map_insertMany (v_as ++ pv_as) as
        doField field = do
                let fvs = getFQTyVarsL (cf_type field) \\ (vs ++ pvs)
                fv_as <- mapM makeAssump fvs
                kcCQTypeStar (map_insertMany fv_as as') (cf_type field)
    mapM_ doField fs
    mapM_ (inferCPred as') ps
    unifyDefStar i con_k v_as mk
inferKDefn as (Cinstance qt@(CQType ps t) _) = do
    as' <- mapM makeAssump (getFQTyVarsL qt)
    let as'' = map_insertMany as' as
    mapM_ (inferCPred as'') ps
    kcCTypeStar as'' t
inferKDefn _ _ = return ()

inferCPred :: Assumps -> CPred -> KI ()
inferCPred as (CPred (CTypeclass i) ts) = kcCTypeStar as (cTApplys (cTCon i) ts)


kcCType :: Assumps -> CType -> KI Kind
kcCType as (TVar (TyVar i _ _)) =
    case M.lookup i as of
    Just k -> return k
    Nothing -> err (getPosition i, EUnboundTyVar (pfpString i))
kcCType as (TCon (TyNum _ _)) = return KNum
kcCType as (TCon (TyStr _ _)) = return KStr
kcCType as (TCon (TyCon i _ _)) =
    case M.lookup i as of
    Just k -> return k
    Nothing -> err (getPosition i, EUnboundTyCon (pfpString i))
kcCType as ct@(TAp f a) = do
    fk <- kcCType as f
    ak <- kcCType as a
    v <- unifyFunc f fk a ak
    return v
kcCType _ t@(TGen _ _) = internalError ("kcCType: TGen")
kcCType _ t@(TDefMonad _) = internalError ("kcCType: TDefMonad")

kcCTypeStar :: Assumps -> CType -> KI ()
kcCTypeStar as t = do
    k <- kcCType as t
    unifyType t k KStar

kcCQTypeStar :: Assumps -> CQType -> KI ()
kcCQTypeStar as (CQType ps t) = do
    mapM_ (inferCPred as) ps
    kcCTypeStar as t


getFQTyVarsL :: CQType -> [Id]
getFQTyVarsL qt = S.toList (getFQTyVars qt)

mustFindK :: Id -> M.Map Id Kind -> Kind
mustFindK i m | (Just k) <- M.lookup i m = k
mustFindK i m = internalError ("InferKind.mustFindK" ++ show i)
