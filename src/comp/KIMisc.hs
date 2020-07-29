{-# LANGUAGE CPP #-}
module KIMisc(
        KVar, KSubst, apKSu,
        KI, run, err, newKVar, getKSubst,
        unifyType, unifyFunc, unifyDefArgs, unifyDefAlias, unifyDefStar,
        groundK) where

import Data.List(union)
import Data.Maybe(fromMaybe)
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 710)
import Control.Applicative(Applicative(..))
#endif
import Control.Monad(when, ap, liftM)
import CVPrint
import PFPrint
import Error(internalError, EMsg, ErrMsg(..))
import CType(baseKVar, isKVar)
import Id(Id, getIdString)
import Util(traceM, tracep)
import IOUtil(progArgs)
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

-- import Debug.Trace

infixr 4 @@

doTraceKI :: Bool
doTraceKI = "-trace-kind-inference" `elem` progArgs

type KVar = Int

data KSubst  = S (IM.IntMap Kind) (IM.IntMap IS.IntSet)

instance Eq KSubst where
  (S s1 _) == (S s2 _) = s1 == s2

instance PPrint KSubst where
    pPrint d p (S s b) = pPrint d p (IM.toList s)

nullKSubst  :: KSubst
nullKSubst   = S IM.empty IM.empty

(+->)      :: KVar -> Kind -> KSubst
u +-> t     = S (IM.singleton u t)
                (back_set u t)

back_set :: KVar -> Kind -> IM.IntMap IS.IntSet
back_set u t = (IM.fromList (map (\v -> (v, IS.singleton u)) (tv t)))

{-
-- Unused
mkKSubst :: [(KVar, Kind)] -> KSubst
mkKSubst vts = S vts
-}

apKSu :: KSubst -> Kind -> Kind
apKSu (S s _) v@(KVar u) =
    case IM.lookup u s of
    Just k  -> k
    Nothing -> v
apKSu s (Kfun l r) = Kfun (apKSu s l) (apKSu s r)
apKSu s KStar = KStar
apKSu s KNum = KNum
apKSu s KStr = KStr

tv :: Kind -> [KVar]
tv (KVar u)   = [u]
tv (Kfun l r) = tv l `union` tv r
tv KStar      = []
tv KNum       = []
tv KStr       = []

(@@) :: KSubst -> KSubst -> KSubst
(S s1 b1) @@ S s2 b2 | IS.null (IS.intersection (IM.keysSet b2)
                                                (IM.keysSet s1)) =
  S (IM.union s1 s2) (IM.unionWith IS.union b1 b2)

-- general case when s1 needs to be applied to the rhs of s2
ss1@(S s1 b1) @@ S s2 b2 = S (IM.union s1 s2') (IM.unionWith IS.union b1 b2')
  where s2' = (IM.map (apKSu ss1) s2)
        b2' = IM.unionWith IS.union b2_base b2_overlap
        b2_base = IM.difference b2 s1
        b2_overlap = (IM.fromListWith IS.union overlap_list_map)
        overlap_vars = IS.toList (IS.intersection (IM.keysSet b2) (IM.keysSet s1))
        get_mtv u = fmap tv (IM.lookup u s1)
        overlap_pairs = [ (u, fromMaybe [] (get_mtv u)) | u <- overlap_vars ]
        overlap_list_map = [ (u, IS.fromList vs) | (u, vs) <- overlap_pairs,
                                                   not (null vs) ]

{-
-- Unused
-- (was the last use removed when fixing fundep handling?)
merge :: KSubst -> KSubst -> Maybe KSubst
merge ss1@(S s1) ss2@(S s2) = if agree then Just (S s) else Nothing
 where dom s = map fst s
       s     = s1 ++ s2
       agree = all (\v -> apKSu ss1 (KVar v) ==
                          apKSu ss2 (KVar v))
                   (dom s1 `intersect` dom s2)
-}

--------------------

mgu  :: Kind -> Kind -> Maybe KSubst
mgu (Kfun l r) (Kfun l' r') = do s1 <- mgu l l'
                                 s2 <- mgu (apKSu s1 r)
                                         (apKSu s1 r')
                                 Just (s2 @@ s1)
mgu (KVar u) t        = varBind u t
mgu t (KVar u)        = varBind u t
mgu KStar KStar       = Just nullKSubst
mgu KNum KNum         = Just nullKSubst
mgu KStr KStr         = Just nullKSubst
mgu t1 t2             = Nothing


varBind :: KVar -> Kind -> Maybe KSubst
varBind u t | t == KVar u      = Just nullKSubst
            | u `elem` tv t    = Nothing
            | otherwise        = Just (u +-> t)

--------------------

data KState = KState KSubst Int

newtype KI a = M (KState -> Either EMsg (KState, a))

instance Monad KI where
    return a = M $ \ s -> Right (s, a)
    M a >>= f = M $ \ s ->
        case a s of
        Left e -> Left e
        Right (s', b) ->
            let M f' = f b
            in  f' s'

instance Functor KI where
  fmap = liftM

instance Applicative KI where
  pure = return
  (<*>) = ap

run :: KI a -> Either EMsg a
run (M m) =
    case m (KState nullKSubst baseKVar) of
    Left e -> Left e
    Right (KState ksubst _, a) ->
        tracep doTraceKI ("KIMisc.run: " ++ ppReadable ksubst) $ Right a

err :: EMsg -> KI a
err e = M (\s->Left e)

getKSubst   :: KI KSubst
getKSubst    = M $
    \ ts@(KState s _) -> Right (ts, s)

extKSubst   :: KSubst -> KI ()
extKSubst s' = M $
    \ (KState s n) -> Right (KState (s'@@s) n, ())

newKVar' :: KI Kind
newKVar' = M $
    \ (KState s n) ->
    Right (KState s (n+1), KVar n)

newKVar :: Maybe Id -> KI Kind
newKVar Nothing = newKVar'
newKVar (Just i) = do
  v <- newKVar'
  when doTraceKI $ traceM ("newKVar: " ++ show (i, v))
  return v

--------------------

-- Unification of type declaration is split into two parts:
-- (1) unify the arguments, and get back a set of assumptions and the
--     result kind (this is "unifyDefArgs")
-- (2) unify the result, after inference has been performed with the
--     assumptions from part 1 ("unifyDefAlias" or "unifyDefStar")

unifyDefArgs :: Id -> Kind -> [Id] -> KI ([(Id, Kind)], Maybe Kind)
unifyDefArgs i con_k vs =
    -- no subst needed
    case (extractFuncArgKinds con_k) of
      [k] | (length vs > 0) && (isKVar k)
          -> -- no kind signature was given (only possible in Classic)
             do vks <- mapM (newKVar . Just) vs
                return (zip vs vks, Nothing)
      ks  -> -- we can assume that a complete kind signature has been given,
             -- but check that the number of argument kinds matches the
             -- number of argument variables (only possible in Classic)
             do let vks = init ks
                    res = last ks
                -- only check for too few; too many will be handled at the
                -- next unification step
                -- XXX we could create a new error tag for this situation
                if (length vs > length vks)
                  then err (getPosition i, ETypeTooManyArgs (pfpString i))
                  else if (length vs == length vks)
                  then return (zip vs vks, Just res)
                  else let (vks1, vks2) = splitAt (length vs) vks
                       in  return (zip vs vks1, Just (mkKFun vks2 res))

-- Unify the result of a type alias declaration
-- This is handled separately, since the result type of the alias does not
-- have to be Star, and we want to report mismatch on the result expression
-- (only matters in Classic, when a kind signature is given).
unifyDefAlias :: Id -> Kind -> [(Id, Kind)] -> Maybe Kind -> Type -> Kind ->
                 KI ()
unifyDefAlias i ck as mk t k_inferred = do
    let aks = map snd as
    case (mk) of
      Nothing -> -- unify the whole kind
                 unifyDef i (mkKFun aks k_inferred) ck
      Just k  -> -- unify the inferred type for the alias expression ("t")
                 -- with the result kind given by the user
                 unifyDefType t k_inferred k

-- Unify the result of a data type declaration (kind Star)
-- This will only fail in Classic, if the user has given a kind signature.
unifyDefStar :: Id -> Kind -> [(Id, Kind)] -> Maybe Kind -> KI ()
unifyDefStar i ck as mk = do
    let aks = map snd as
    case (mk) of
      Nothing -> -- unify the whole kind
                 unifyDef i (mkKFun aks KStar) ck
      Just k  -> -- unify just the result kind
                 unifyDef i KStar k

extractFuncArgKinds :: Kind -> [Kind]
extractFuncArgKinds (Kfun a b) = (a : extractFuncArgKinds b)
extractFuncArgKinds k = [k]

mkKFun :: [Kind] -> Kind -> Kind
mkKFun []     k = k
mkKFun (a:as) k = Kfun a (mkKFun as k)

kindErr :: Type -> Kind -> Kind -> ErrMsg
kindErr t KStar KNum  = EKindNumForStar (pfpString t)
kindErr t KStar KStr  = EKindStrForStar (pfpString t)
kindErr t KNum  KStar = EKindStarForNum (pfpString t)
kindErr t KNum  KStr  = EKindStrForNum (pfpString t)
kindErr t KStr  KStar = EKindStarForStr (pfpString t)
kindErr t KStr  KNum  = EKindNumForStr (pfpString t)
-- XXX replace Readable with String
kindErr t exp   inf   = EUnifyKind (pfpReadable t) (ppReadable inf) (ppReadable exp)


-- The following two functions are like "unifyType", except that they do
-- not report errors about being applied to too many or too few arguments.
-- In BSV, that situation cannot occur; in Classic, it only occurs if the
-- user has given a bad kind signature and there we want to report the usual
-- kind-mismatch error.
-- XXX We could have a special error for type def kind signature mismatch,
-- XXX instead of using EUnifyKind.

-- This one does not report special errors about numeric vs string vs value.
-- The only situation where that should occur is for type aliases, and
-- that's handled with "unifyDefType".
unifyDef :: Id -> Kind -> Kind -> KI ()
unifyDef i k_inferred k_expected = do
    s <- getKSubst
    let k_inferred' = apKSu s k_inferred
        k_expected' = apKSu s k_expected
    case mgu k_inferred' k_expected' of
     Just u  -> extKSubst u
     Nothing ->
         -- XXX replace Readable with String
         err (getPosition i, EUnifyKind (pfpReadable i)
                                (ppReadable k_inferred')
                                (ppReadable k_expected'))

-- This reports the error on the alias expression, and reports numeric,
-- string and value kinds specially.
unifyDefType :: Type -> Kind -> Kind -> KI ()
unifyDefType t k_inferred k_expected = do
    s <- getKSubst
    let k_inferred' = apKSu s k_inferred
        k_expected' = apKSu s k_expected
    case mgu k_inferred' k_expected' of
     Just u  -> extKSubst u
     Nothing -> err (getPosition t, kindErr t k_expected' k_inferred')


-- Takes the function and its kind and the argument to which the function
-- is applied and the arguments kind, and returns the newKVar
unifyFunc :: Type -> Kind -> Type -> Kind -> KI Kind
unifyFunc f fk a ak = do
    s <- getKSubst
    let sfk = apKSu s fk
        sak = apKSu s ak
    -- trace "unifyFunc:" $ return ()
    case sfk of
        Kfun ak' v' -> do
                         -- The function has inferred kind "ak' -> ..."
                         -- so use "ak'" as the expected kind for the argument
                         unifyType a sak ak'
                         -- Return the inferred result
                         return v'
        _ -> do v <- newKVar Nothing
                -- The function is expected to be "sak -> ..."
                unifyType f sfk (Kfun sak v)
                return v


unifyType :: Type -> Kind -> Kind -> KI ()
unifyType t k_inferred k_expected = do
    s <- getKSubst
    let k_inferred' = apKSu s k_inferred
        k_expected' = apKSu s k_expected
    case mgu k_inferred' k_expected' of
     Just u  -> extKSubst u
     Nothing ->
       let
           pos = getPosition t

           -- if a type constructor is being partially applied, get the core
           unapType = removeTypeAps t
           -- the name of the constructor, for error messages
           unapTypeName = showUnapType t
       in
         -- trace ("trace: unifyType: " ++ traceUnapType t) $
           if (isGroundNonFuncK k_inferred') && (isFuncK k_expected')
           then
             -- handle case of too many arguments
             case unapType of
                 TCon (TyNum i _) -> err (pos, ENumKindArg)
                 _ -> if (unapType == t)
                      then -- type is not partially applied
                        err (pos, ETypeNoArg unapTypeName)
                      else
                          err (pos, ETypeTooManyArgs unapTypeName)
           else
           if (isGroundNonFuncK k_expected') && (isFuncK k_inferred')
           then
             -- handle case of not enough arguments
             err (pos, ETypeTooFewArgs unapTypeName)
           else
           err (getPosition t, kindErr t k_expected' k_inferred')

--------------------

groundK :: Kind -> Kind
groundK KStar = KStar
groundK KNum = KNum
groundK KStr = KStr
groundK (Kfun l r) = Kfun (groundK l) (groundK r)
groundK (KVar k) = tracep doTraceKI ("groundK: " ++ show k) $ KStar

--------------------

-- This is like "leftCon", except that it returns the inner type
-- even when it's not a "TyCon"
removeTypeAps :: Type -> Type
removeTypeAps (TAp f _) = removeTypeAps f
removeTypeAps t = t

-- The unapplied type as a String, for error messages
showUnapType :: Type -> String
showUnapType t =
    case (removeTypeAps t) of
      TCon (TyCon i _ _) -> getIdString i
      TCon (TyNum i _) -> show i
      TCon (TyStr s _) -> show s
      TVar (TyVar i _ _) -> getIdString i
      unapType@(TGen _ _) -> show unapType
      -- These shouldn't happen
      TAp _ _ -> internalError "KIMisc.showUnapType (TAp)"
      TDefMonad _ -> internalError "KIMisc.showUnapType (TDefMonad)"

{-
-- The unapplied type as a String, for debug trace
traceUnapType :: Type -> String
traceUnapType t =
    case (removeTypeAps t) of
      TCon (TyCon i _ _) -> "TCon (TyCon) " ++ getIdString i
      TCon (TyNum i _) -> "TCon (TyNum) " ++ show i
      TVar (TyVar i _ _) -> "TVar " ++ getIdString i
      TGen _ _ -> "TGen"
      -- These shouldn't happen
      TAp _ _ -> "TAp"
      TDefMonad _ -> "TDefMonad"
-}

-- Returns whether a kind is grounded (has no variables) and is not
-- a function; i.e. a value, num or string kind.
isGroundNonFuncK :: Kind -> Bool
isGroundNonFuncK KStar = True
isGroundNonFuncK KNum  = True
isGroundNonFuncK KStr  = True
isGroundNonFuncK _     = False

-- Returns whether a kind is a function
isFuncK :: Kind -> Bool
isFuncK (Kfun _ _) = True
isFuncK _          = False

--------------------
