module TypeAnalysis (
                     TypeAnalysis(..),
                     analyzeType,
                     analyzeType',
                     showType,
                     getWidth,

                     -- to be used with showType
                     kVector, vsVector, kList, vsList
                     ) where

import Data.List(genericDrop, intercalate, (\\), nub, sortBy)
import Data.Char(isUpper)

import Util(doRight, itos)
import Error(internalError, EMsg, ErrMsg(..))
import Flags
import Classic
import PFPrint
import Position(getPosition,noPosition)
import Id
import PreIds
import Pragma
import CType
import CSyntax(IdK(..))
import Type
import Assump
import Pred
import Scheme
import SymTab
import MakeSymTab(convCType)
import TIMonad as TI
import TCMisc(satisfy, mkVPredFromPred, expandSynN)
import Subst


-- ---------------

data TypeAnalysis =
      Unknown
    -- These we handle by reporting an EMsg:
    -- | OverApplied
    -- | UnderApplied
    | Variable
    | Function
    | Numeric
    | String
    | Primary     Id Kind [Id] Bool (Maybe Integer)
    | Vector      Bool CType CType (Maybe Integer)
    | List        Bool CType
    | Alias       Id Kind [Id] CType
    | Struct      Id Kind [Id] Bool [(Id, Qual Type, Maybe Integer)] (Maybe Integer)
    | Enum        Id [Id] (Maybe Integer)
    | TaggedUnion Id Kind [Id] Bool [(Id, Type, Maybe Integer)] (Maybe Integer)
    | Interface   Id Kind [Id] Bool [(Bool, Id, Qual Type, [IfcPragma])] [IfcPragma]
    | Typeclass   Id Kind [Id] [Type] [[Bool]] (Maybe Bool) [Qual Type] [(Id, Qual Type)]


-- ---------------

getWidth :: TypeAnalysis -> Maybe Integer
getWidth (Primary _ _ _ _ mi)       = mi
getWidth (Vector _ _ _ mi)          = mi
getWidth (Struct _ _ _ _ _ mi)      = mi
getWidth (Enum _ _ mi)              = mi
getWidth (TaggedUnion _ _ _ _ _ mi) = mi
getWidth _                          = Nothing

showType :: Bool -> Id -> Kind -> [Id] -> String
showType showKinds t k user_vs =
    let
        showT
         | isClassic() && showKinds = pfStr $ IdKind t k
         | otherwise = pfStr t
        arg_ks = getArgKinds k
        arg_names =
            let user_arg_names = map getIdString user_vs
            in  user_arg_names ++ (inexhaustable_var_names \\ user_arg_names)
        showArg :: Bool -> Kind -> String -> String
        showArg True arg_k name =
            (case arg_k of
               KNum -> "numeric "
               KStr -> "string "
               _ -> "") ++ "type " ++ name
        showArg False arg_k name = name
        showArgs
          | isClassic() = unwords ("" : take (length arg_ks) arg_names)
          | otherwise =
            "#" ++ inParens
                     (commaSep
                         (zipWith (showArg showKinds) arg_ks arg_names))
    in showT ++ (if null arg_ks then [] else showArgs)


-- make [a,...,z,aa,ab,...,zy,zz,aaa,...]
inexhaustable_var_names :: [String]
inexhaustable_var_names = names
  where
    names = [ x:r | r <- ([]:names),
                    x <- ['a'..'z'] ]


-- Given a list of type arguments already supplied
-- and a list of kinds for the remaining generic types,
-- produce a list of tyvars to substitute for those remaining types
-- (which doesn't clash with any names in the supplied types).
addGenVars :: [Type] -> [Kind] -> [Type]
addGenVars as ks =
   let
       given_tyvar_names = nub $ map (getIdBaseString . getTyVarId) (tv as)
       additional_names = inexhaustable_var_names \\ given_tyvar_names
       additional_ids = map mk_homeless_id additional_names
       additional_tyvars = zipWith cTVarKind additional_ids ks
   in
       as ++ additional_tyvars

-- ---------------

analyzeType :: Flags -> SymTab -> CType -> Either [EMsg] TypeAnalysis
analyzeType flags symtab unqual_ty = analyzeType' flags symtab unqual_ty False

analyzeType' :: Flags -> SymTab -> CType -> Bool -> Either [EMsg] TypeAnalysis
analyzeType' flags symtab unqual_ty primpair_is_interface = doRight analyze (kindCheck unqual_ty)
  where
    w = getBitWidth flags symtab

    kindCheck :: CType -> Either [EMsg] CType
    kindCheck t =
        -- "convCType" will error on too-many-args,
        -- but we have to detect too-few-args
        case (convCType symtab t) of
          Left err -> Left [err]
          Right t' ->
              case (kind t') of
                Kfun _ _ ->
                    let unapTypeName = ppString $ fst (splitTAp t)
                    in  Left [(getPosition t, ETypeTooFewArgs unapTypeName)]
                k -> Right t'

    analyze :: CType -> Either [EMsg] TypeAnalysis
    analyze t =
       case (splitTAp t) of
         (TVar {}, as) -> Right Variable
         (TDefMonad {}, as) ->
             -- need more context
             Right Variable  -- Unknown?
         (TGen {}, as) -> internalError "analyzeType': found TGen"
         (TAp {}, as)  -> internalError "analyzeType': found TAp"
         (TCon (TyNum n pos), as) ->
             if (null as)
             then Right Numeric
             else -- Right OverApplied
                  -- (this can't happen, because kindCheck catches it)
                  Left [(pos, ENumKindArg)]
         (TCon (TyStr s pos), as) ->
             if (null as)
             then Right String
             else -- Right OverApplied
                  -- (this can't happen, because kindCheck catches it)
                  Left [(pos, EStrKindArg)]
         (TCon (TyCon i _ _), as) ->
             -- the other fields are bogus before typechecking
             analyzeTCon t i as

    analyzeTCon :: CType -> Id -> [CType] -> Either [EMsg] TypeAnalysis
    analyzeTCon t i as | (i == idArrow noPosition) =
        -- XXX check for full application?
        Right Function
    analyzeTCon t i as =
       -- look up the type
       case (findType symtab i) of
         Nothing -> Right Unknown
         Just (TypeInfo Nothing k vs ti _) ->
            internalError "analyzeType': value type without Id"
         Just (TypeInfo (Just qi) k vs tisort _) ->
            let isConcrete = null (tv as)
            in  analyzeNonNumTCon t qi k vs as isConcrete tisort

    analyzeNonNumTCon :: CType -> Id ->
                         Kind -> [Id] -> [CType] -> Bool -> TISort ->
                         Either [EMsg] TypeAnalysis
    -- interface
    analyzeNonNumTCon t qi k vs as isC (TIstruct (SInterface pragmas) fields) =
        if (qi == idPrimPair && (not primpair_is_interface))
        then Right $ Primary qi k vs isC (w t)
        else
          let fieldInfos = map (getFieldInfo symtab qi) fields
              mkTuple (FieldInfo _ _ _ (fid :>: (Forall ks qt)) fpragmas _ morigtype _) =
                  let as' = addGenVars as ks
                      fqtype@(ps :=> ft) =
                          apType (expandSynN flags symtab . rmStructArg) (inst as' qt)
                      is_subifc = isSubInterface ft &&
                                  -- subinterfaces have no provisos
                                  -- XXX this check might be unnecessary
                                  null ps
                  in  (is_subifc, fid, fqtype, fpragmas)
          in  Right $ Interface qi k vs isC (map mkTuple fieldInfos) pragmas
    -- struct
    analyzeNonNumTCon t qi k vs as isC (TIstruct SStruct fields) =
        if (qi == idActionValue)
        then Right $ Primary qi k vs isC Nothing
        else if (qi == idPrimUnit)
        then Right $ Primary qi k vs isC (w t)
        else analyzeStructCon t qi k vs as isC fields
    -- type alias (n is the number of type parameters)
    analyzeNonNumTCon t qi k vs as isC (TItype n t') =
        if (qi == idAction)
        then Right $ Primary qi k vs isC Nothing
        else if (qi == idTuple2) || (qi == idTuple3) ||
                (qi == idTuple4) || (qi == idTuple5) ||
                (qi == idTuple6) || (qi == idTuple7) ||
                (qi == idTuple8)
        then --Right $ Primary qi k vs isC (w t)
             let -- XXX assume "as" is the same size as the tuple
                 sz = length as
                 mkField :: (CType, Int) -> (Id, Qual CType, Maybe Integer)
                 mkField (t,n) = let i = mk_homeless_id ("tpl_" ++ itos n)
                                 in  (i, [] :=> t, w t)
                 fs = map mkField (zip as [1..])
             in  Right $ Struct qi k (vsTuple sz) isC fs (w t)
        else
          -- replace the generic types with the specific ones given
          -- by the user, when reporting the alias type
          -- (since the alias may not use all of the arguments,
          -- we should apply the remaining ones)
          let inst_t' = expandSynN flags symtab (inst as t')
              unused_as = genericDrop n as
          in  Right $ Alias qi k vs (cTApplys inst_t' unused_as)
    -- enum / tagged union
    analyzeNonNumTCon t qi k vs as isC (TIdata constructors is_enum) =
        if (qi == idInt)
        then Right $ Primary qi k vs isC (w t)
        else if (qi == idUInt)
        then Right $ Primary qi k vs isC (w t)
        else if (qi == idFile)
        then Right $ Primary qi k vs isC (w t)
        else if (qi == idList)
        then
          case (as) of
              [el] -> Right $ List isC el
              _ -> internalError ("analyzeType': unexpected List params: " ++
                                  ppReadable as)
        else if (qi == idVector)
        then
          case (as) of
              [len,el] -> Right $ Vector isC len el (w t)
              _ -> internalError ("analyzeType': unexpected Vector params: " ++
                                  ppReadable as)
        else
          let conInfos = map (getConInfo symtab qi) constructors
              getConType (ConInfo { ci_assump = (i :>: (Forall ks (ps :=> t))) }) = t
              getConName (ConInfo { ci_assump = (i :>: _) }) = i
          in
              -- figure out if it's enum or tagged union
              if (is_enum)
              then Right $ Enum qi (map getConName conInfos) (w t)
              else let -- we assume that 'ps' is empty (should we check?)
                       mkTuple ci =
                           let (tagT, unionT) = getUnionTypes (getConType ci)
                               new_as = reorderUnionTypeArgs unionT as
                               tf = expandSynN flags symtab $ inst new_as tagT
                           in  (getConName ci, tf, w tf)
                   in  Right $
                         TaggedUnion qi k vs isC (map mkTuple conInfos) (w t)
    -- abstract
    analyzeNonNumTCon t qi k vs as isC (TIabstract) =
        -- XXX if (k == KNum), should we return Numeric?
        -- XXX such as for TAdd etc?  Should TAdd#(1,2) return 3?
        Right $ Primary qi k vs isC (w t)
    -- anonymous struct in Classic tagged union
    analyzeNonNumTCon t qi k vs as isC (TIstruct (SDataCon _ _) fields) =
        analyzeStructCon t qi k vs as isC fields
    -- polymorpic field wrapper
    analyzeNonNumTCon t qi k vs as isC (TIstruct (SPolyWrap _ _ _) fields) =
      analyzeStructCon t qi k vs as isC fields
    -- type class
    analyzeNonNumTCon t qi k vs as isC (TIstruct SClass fields) =
        let
            cls = mustFindClass symtab (CTypeclass qi)
            -- for now, ignore the types provided by the user and just give
            -- the generic info for this typeclass
            orig_as = map TVar (csig cls)

            -- filter out the superclass members
            fields' = let isField (c:cs) | isUpper c = False
                          isField _                  = True
                      in  filter (isField . getIdBaseString) fields
            fieldInfos = map (getFieldInfo symtab qi) fields'
            mkPair (FieldInfo _ _ _ (i :>: (Forall ks qt)) _ _ _ _) =
                let as' = addGenVars orig_as ks
                    qt' = apType (expandSynN flags symtab . rmStructArg) (inst as' qt)
                in  (i, qt')

            ps = map (predToType . snd) (super cls)
            fdeps = funDeps cls
            insts = let mkInst (Inst _ _ (qs :=> p) _) = (qs :=> predToType p)
                    in  map mkInst (getInsts cls)
            allow = allowIncoherent cls
        in  Right $ Typeclass qi k vs ps fdeps allow insts (map mkPair fieldInfos)

    analyzeStructCon :: CType -> Id ->
                        Kind -> [Id] -> [CType] -> Bool -> [Id] ->
                        Either [EMsg] TypeAnalysis
    analyzeStructCon t qi k vs as isC fields =
        let fieldInfos = map (getFieldInfo symtab qi) fields
            mkPair (FieldInfo _ _ _ (i :>: (Forall ks qt)) _ _ _ _) =
                  let as' = addGenVars as ks
                      qt' = apType (expandSynN flags symtab . rmStructArg) (inst as' qt)
                      t = qualToType qt'
                  in (i, qt', w t)
        in  Right $ Struct qi k vs isC (map mkPair fieldInfos) (w t)


-- ---------------

-- Symbol table utilities


-- this expects not to fail to find the constructor info
getConInfo :: SymTab -> Id -> Id -> ConInfo
getConInfo symtab ty con =
    case (findCon symtab con) of
      Nothing -> internalError ("findConInfo: not found: " ++ ppReadable con)
      Just [ci] -> ci
      Just cis ->
          case [ ci | ci@(ConInfo { ci_id = i }) <- cis, qualEq ty i ] of
              [ci] -> ci
              []   -> internalError ("findConInfo: not found: " ++
                                     ppReadable con)
              _    -> internalError ("findConInfo: ambiguous: " ++
                                     ppReadable (con,ty))


-- this expects not to fail to find the field info
getFieldInfo :: SymTab -> Id -> Id -> FieldInfo
getFieldInfo symtab ty field =
    case (findFieldInfo symtab ty field) of
      Nothing -> internalError ("findFieldInfo: not found: " ++
                                ppReadable field)
      Just fi -> fi


-- The type must have already had "convCType" applied to it, for the
-- predicate reduction to work
getBitWidth :: Flags -> SymTab -> CType -> Maybe Integer
getBitWidth flags symtab t =
    case (findSClass symtab (CTypeclass idBits)) of
        Nothing -> Nothing -- Prelude hasn't been loaded :)
        -- Bits is a coherent typeclass
        Just c -> case (fst $ TI.runTI flags False symtab (getBitWidthM c)) of
                      Right r -> r
                      Left _  -> Nothing
  where
    getBitWidthM :: Class -> TI (Maybe Integer)
    getBitWidthM bitsCls = do
        {- Do this, if you want to return a parameterized width
          -- record any vars in the type,
          -- so that we preserve names as given by the user
          addBoundTVs (tv t)
        -}
        -- construct the proviso Bits#(t,szv) for a new var 'szv'
        szv <- newTVar "getBitWidth" KNum t
        let p = IsIn bitsCls [t, szv]
        vp <- mkVPredFromPred [] p
        -- try to satisfy the proviso
        {- Do this, if you want to return a parameterized width
          -- (use FV version, to allow TAdd/TMul in the result)
          (rs,_) <- satisfyFV [] [] [vp]
        -}
        (rs,_) <- satisfy [] [vp]
        s <- getSubst
        let szv' = apSub s szv
        -- if it was satisfiable, then apply the substitution to 'szv'
        -- and that is the width
        return $
            -- if parameterized width is desired, then allow non TyNum
            -- here as well (it could be a TyVar of TAp of TMul/TAdd/etc)
            if (null rs) && (isTNum szv')
            then Just (getTNum szv')
            else Nothing


-- ---------------

-- Type utilities

kVector, kList :: Kind
kVector = Kfun KNum (Kfun KStar KStar)
kList   = Kfun KStar KStar

vsVector, vsList :: [Id]
vsVector = map mk_homeless_id ["vsize", "element_type"]
vsList   = map mk_homeless_id ["element_type"]

vsTuple :: Int -> [Id]
vsTuple sz = if sz > 8
             then internalError ("vsTuple: size > 7: " ++ ppReadable sz)
             else map mk_homeless_id (take sz ["a","b","c","d","e","f","g","h"])

-- apply a function to the base of a qualified type
apType :: (Type -> Type) -> Qual Type -> Qual Type
apType f (ps :=> t) = ps :=> f t

-- Whether a type is a valid subinterface type
-- (and should be marked "interface" and not "method").
isSubInterface :: CType -> Bool
isSubInterface t =
    case (leftCon t, tyConArgs t) of
      (Just con, []) | (qualEq con idClock) -> True
      (Just con, []) | (qualEq con idReset) -> True
      (Just con, [_]) | (qualEq con idInout) -> True
      (Just con, [TCon (TyNum n _), elem_t])
          | ((qualEq con idListN) || (qualEq con idVector))
        -> isSubInterface elem_t
      _ -> isInterface t

-- For struct and interfaces, the fields take the struct/ifc as the
-- first argument.  So we remove that argument when displaying the
-- type as the user knows it.
-- XXX should we do more to check that the first argument is the struct type?
rmStructArg :: CType -> CType
rmStructArg (TAp (TAp (TCon arr) c) t) | (isTConArrow arr) = t
rmStructArg t = internalError ("rmStructArg: no arrow: " ++ ppReadable t)

{-
-- For tagged unions, get the type of the field, which is the argument.
rmUnionRes :: CType -> CType
rmUnionRes unionT =
    case (getArrows unionT) of
        ([argT], _) -> argT
        _ -> internalError ("rmUnionRes: wrong kind: " ++ ppReadable unionT)
-}

-- For tagged unions, get the type of the field, which is the argument;
-- but also return the tagged union type (the result), for adjusting
-- the type arguments into the proper order
getUnionTypes :: CType -> (CType, CType)
getUnionTypes unionT =
    case (getArrows unionT) of
        ([argT], resT) -> (argT, resT)
        _ -> internalError ("getUnionTypes: wrong kind: " ++ ppReadable unionT)

-- reorder the type arguments to a polymorphic tagged union type,
-- to match the order in which they are generalized in the scheme for
-- one of the tags
reorderUnionTypeArgs :: CType -> [CType] -> [CType]
reorderUnionTypeArgs unionT as =
    let ts = tyConArgs unionT
        getGenIdx (TGen _ n) = n
        getGenIdx t = internalError ("reorderUnionTypeArgs: not Gen: " ++
                                     ppReadable t)
        nas = zip (map getGenIdx ts) as
        cmpFn (n1,_) (n2,_) = compare n1 n2
    in
        map snd (sortBy cmpFn nas)


-- ---------------

-- String utilities

pfStr :: (PPrint a, PVPrint a) => a -> String
pfStr = pfpString

inParens :: String -> String
inParens s = "(" ++ s ++ ")"

commaSep :: [String] -> String
commaSep = intercalate ", "


-- ---------------
