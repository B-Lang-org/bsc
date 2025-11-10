{-# LANGUAGE PatternGuards #-}
module ISyntaxCheck(iGetKind,
                    tCheckIPackage,
                    tCheckIModule) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified EquivalenceClass as EC

import ErrorUtil(internalError)
import Flags(Flags)
import PPrint hiding(empty)
import Position
import Id
import PreIds
import ISyntax
import ISyntaxSubst(tSubst)
import ISyntaxUtil
import SymTab(SymTab, mustFindClass, findSClass)

import Pred
import CType
import TCMisc
import TIMonad

import IOUtil(progArgs)
import Util(tracep, fromJustOrErr)

doTraceEqWitnesses :: Bool
doTraceEqWitnesses = "-trace-eq-witnesses" `elem` progArgs

trace_witness :: String -> a -> a
trace_witness = tracep doTraceEqWitnesses

-----

eqType :: Flags -> SymTab -> Env -> IType -> IType -> Bool
eqType flags symt r (ITForAll i k t) (ITForAll i' k' t') =
    k == k' &&
    eqType flags symt (addK i k r) t (tSubst i' (ITVar i) t')
eqType flags symt r t t' = eqType0 flags symt r t t'

eqType0 :: Flags -> SymTab -> Env -> IType -> IType -> Bool
eqType0 flags symt r@(E _ _ eqs _) t t' =
    --trace ("eqType0 " ++ ppReadable(t,t')) $
    t == t' ||
    EC.isEqual eqs t t' ||
    eqType1 flags symt r t t' ||
    -- try satisfying NumEq
    -- XXX this is wasted work when the kind is not numeric
    eqTypeFinal flags symt r t t'

eqType1 :: Flags -> SymTab -> Env -> IType -> IType -> Bool

-- hack to make commutative type constructors work
eqType1 flags symt r (ITAp (ITAp (ITAp (ITCon i _ _) t1) t2) t3)
                     (ITAp (ITAp (ITAp (ITCon i' _ _) t1') t2') t3')
    | (i == i') && (hasIdProp i IdPCommutativeTCon) =
    eqType0 flags symt r t3 t3' &&
    (((eqType0 flags symt r t1 t1') && (eqType0 flags symt r t2 t2')) ||
     ((eqType0 flags symt r t1 t2') && (eqType0 flags symt r t2 t1')))

-- look for arrows and add any dictionaries
eqType1 flags symt r (ITAp (ITAp (ITCon tc _ _) tA) tB)
                     (ITAp (ITAp (ITCon tc' _ _) tA') tB')
    | (tc == idArrow noPosition) && (tc' == idArrow noPosition) =
    let r2 = addDict symt tA r
    in  eqType0 flags symt r tA tA' && eqType0 flags symt r2 tB tB'

eqType1 flags symt r (ITAp f a) (ITAp f' a') =
    eqType0 flags symt r f f' && eqType0 flags symt r a a'
eqType1 _ _ _ (ITVar i) (ITVar i') = i == i'
eqType1 _ _ _ (ITCon i _ _) (ITCon i' _ _) = i == i'
eqType1 _ _ _ (ITNum n) (ITNum n') = n == n'
eqType1 _ _ _ _ _ = False

-- Decide if two (numeric) types are equal by creating a NumEq proviso
-- in CSyntax and applying "satisfy".
eqTypeFinal :: Flags -> SymTab -> Env -> IType -> IType -> Bool
eqTypeFinal flags symt e t1 t2
    -- Attempt to save time by weeding out cases without TAdd, SizeOf, etc
    -- (since there's no use trying to equate "n" and "m", for instance)
    -- XXX can we also weed out when the kind is not numeric?
    | isITAp t1 || isITAp t2 =
    let numEqCls = mustFindClass symt (CTypeclass idNumEq)
        (e', t1') = convType e t1
        (E _ _ _ (PredEnv _ m s), t2') = convType e' t2
        --satisfyEq :: TI ([VPred], [CDefl])
        satisfyEq = do
          eqs <- mapM mkEPred (S.toList s)
          addBoundTVs (M.elems m)
          addExplPreds eqs
          vp <- mkVPredFromPred [] (IsIn numEqCls [t1', t2'])
          satisfy eqs [vp]
    in  case (fst $ runTI flags False symt satisfyEq) of
          Right ([],_) -> True
          res -> --trace("eqTypeFinal: not satisfied: " ++ ppReadable res) $
                 False
 where isITAp (ITAp _ _) = True
       isITAp _          = False
eqTypeFinal _ _ _ _ _ = False

-------

assert :: (PPrint e, Show t) => Bool -> String -> e -> t -> a -> a
assert True  s e t x = x
assert False s e t x = internalError ("assert failed: " ++ s ++ "\n" ++ ppReadable e ++ "\n" ++ (show t))
--assert False s e x = internalError ("assert failed: " ++ s ++ "\n" ++ ppDebug e)

type EqTy = Env -> IType -> IType -> Bool

tCheck :: SymTab -> Env -> EqTy -> IExpr a -> IType
tCheck symt r eqTy ec@(ILam i t e) =
    -- assert (kCheckErr r t == IKStar) "ILam" (ec, kCheckErr r t) $
        itFun t (tCheck symt (addT symt i t r) eqTy e)
tCheck symt r eqTy ec@(IAps f0 ts [a]) =
        let f = iAps f0 ts [] in
        case tCheck symt r eqTy f of
        ITAp (ITAp arr at') rt | arr == itArrow ->
            let at = tCheck symt r eqTy a
            in  -- This trace can lead to infinite loops.
                --trace("tCheck " ++ ppReadable((f,tCheck symt r eqTy f),(a,at))) $
                assert (eqTy r at at') "IAp"
                    (r, ec, a, (at, at') {-, (f,ft),(a,at)-}) (at, at') rt
        tt -> internalError ("tCheck IAp: " ++ ppReadable(ec, f, tt))
tCheck symt r eqTy (IAps f ts (e:es)) =
    tCheck symt r eqTy (IAps (IAps f ts [e]) [] es)
tCheck symt r _ (IVar i) = findT i r
tCheck symt r eqTy (ILAM i k e) =
    ITForAll i k (tCheck symt (addK i k r) eqTy e)
tCheck symt r eqTy ec@(IAps e [t] []) =
        case tCheck symt r eqTy e of
        --et@(ITForAll i k rt) ->
        ITForAll i k rt ->
            let kt = kCheckErr r t
                rt'= tSubst i t rt
            in  --trace ("tCheck " ++ ppReadable ((e,et),(t,kt))) $
                assert (k == kt) "IAP" (ec, (i,k,rt), kt) (k, kt) rt'
        tt -> internalError ("tCheck IAP: " ++ ppReadable (ec, tt))
tCheck symt r eqTy (IAps f (t:ts) []) =
    tCheck symt r eqTy (IAps (IAps f [t] []) ts [])
tCheck symt r _ (ICon c ic) = iConType ic
tCheck symt r eqTy (IAps f [] []) =
    -- trace ("tCheck " ++ show f) $
    tCheck symt r eqTy f
tCheck symt r _ (IRefT t _ _) = t
--tCheck _ _ _ e = internalError ("no match in tCheck: " ++ ppReadable e)

kCheck :: Env -> IType -> Maybe IKind
kCheck r (ITForAll i k t) = do
  kr <- kCheck (addK i k r) t
  return (IKFun k kr)
kCheck r tc@(ITAp f a) = do
  kf <- kCheck r f
  case kf of
    IKFun ka kr ->
        do ka' <- kCheck r a
           assert (ka' == ka) "ITAp" (tc, (f, kf), (ka', ka)) (ka', ka) $ return kr
    k -> internalError ("kCheck " ++ ppReadable (tc, k))
kCheck r (ITVar i) = findK i r
kCheck r (ITCon _ k _) = return k
kCheck r (ITNum _) = return IKNum
kCheck r (ITStr _) = return IKStr

iGetKind :: IType -> Maybe IKind
iGetKind = kCheck emptyEnv

kCheckErr :: Env -> IType -> IKind
kCheckErr r t = fj $ kCheck r t
  where fj = fromJustOrErr ("findK: " ++ ppReadable (r, t))

tCheckIPackage :: Flags -> SymTab -> IPackage a -> Bool
tCheckIPackage flags symt (IPackage pi _ _ ds) =
    let r  = emptyEnv
        defOK (IDef i t e _) =
            let t' = tCheck symt r (eqType flags symt) e
            in  assert (eqType flags symt r t' t) "defOK1"
                    (i,e,(t,t')) (t, t') True
    in  all defOK ds

tCheckIModule :: Flags -> SymTab -> IModule a -> Bool
tCheckIModule flags symt (IModule { imod_type_args  = iks,
                                    imod_local_defs = ds,
                                    imod_rules      = rs,
                                    imod_interface  = ifc }) =
        let eqTy _ = (==) -- Just direct equality, no other manipulations.
            r = foldr (\ (i, k) r -> addK i k r) emptyEnv iks
            defOK (IDef i t e _) =
                let t' = tCheck symt r eqTy e
                in  assert (t == t') "defOK2"
                        (i,e,(t,t')) (t, t') True
            ifcOK (IEFace i _ maybe_e maybe_r _ _) =
                       (case maybe_e of
                          Just (e,t) -> defOK (IDef i t e [])
                          _ -> True)
                       &&
                       (case maybe_r of
                          Just rs -> rulesOK rs
                          _ -> True)

            rulesOK (IRules sps rs) = all ruleOK rs
            ruleOK (IRule { irule_pred = p , irule_body = a }) =
                let tp = tCheck symt r eqTy p
                    ta = tCheck symt r eqTy a
                in
                    assert (tp == itBit1) "ruleOK p"
                        (p, tp) (p, tp) True &&
                    assert (ta == itAction) "ruleOK a"
                        (a, ta) (p, tp) True
        in  all defOK ds && rulesOK rs && all ifcOK ifc

-------

data Env = E (M.Map Id IType) (M.Map Id IKind) (EC.EquivClasses IType) PredEnv

emptyEnv :: Env
emptyEnv = E M.empty M.empty EC.empty emptyPredEnv

addDict :: SymTab -> IType -> Env -> Env
addDict symt t e@(E tm km eqs ps) = E tm km eqs' ps'
  where new_eqs = case t of
                    (ITAp (ITAp (ITCon i _ _) t1) t2)
                         | i == idLog   -> [(ITAp iTLog t1, t2)]
                         | i == idBits  -> [(ITAp iTSizeOf t1, t2)]
                         | i == idNumEq -> [(t1, t2)]
                    (ITAp (ITAp (ITAp (ITCon i _ _) t1) t2) t3)
                         -- XXX should we also equate T#(t2,t1)
                         | i == idAdd -> [(ITAp (ITAp iTAdd t1) t2, t3)]
                         | i == idMax -> [(ITAp (ITAp iTMax t1) t2, t3)]
                         | i == idMin -> [(ITAp (ITAp iTMin t1) t2, t3)]
                         | i == idMul -> [(ITAp (ITAp iTMul t1) t2, t3)]
                         | i == idDiv -> [(ITAp (ITAp iTDiv t1) t2, t3)]
                    otherwise -> []
        eqs' = trace_witness ("num eq witnesses: " ++ ppReadable new_eqs) $
               let eqFn (x,y) ec = EC.equate x y ec
               in  foldr eqFn eqs new_eqs
        ps' = addPred symt e t

addT :: SymTab -> Id -> IType -> Env -> Env
addT symt i t (E tm km eqs ps) = addDict symt t $ E (M.insert i t tm) km eqs ps

addK :: Id -> IKind -> Env -> Env
addK i k (E tm km eqs ps) = E tm (M.insert i k km) eqs ps

findT :: Id -> Env -> IType
findT i (E tm _ _ _) =
    case M.lookup i tm of
        Just t -> t
        Nothing -> internalError ("ISyntaxCheck.findT " ++ ppString i ++ "\n" ++ ppReadable (M.toList tm))

findK :: Id -> Env -> Maybe IKind
findK i (E _ km _ _) = M.lookup i km

instance PPrint Env where
    pPrint d _ (E tm km eqs ps) =
        text "Env" <+>
        (pPrint d 0 (M.toList tm) $$
         pPrint d 0 (M.toList km) $$
         pPrint d 0 (EC.classes eqs) $$
         text "PredEnv")

------

data PredEnv = PredEnv Int (M.Map Id TyVar) (S.Set Pred.Pred)

emptyPredEnv :: PredEnv
emptyPredEnv = PredEnv 0 M.empty S.empty

convType :: Env -> IType -> (Env, Type)
convType _ (ITForAll i k t) = internalError ("convType: ITForAll " ++ ppReadable (i, k, t))
convType e (ITAp t1 t2) =
    let (e', t1') = convType e t1
        (e'', t2') = convType e' t2
    in  (e'', TAp t1' t2')
convType e@(E tm km eqs (PredEnv n m s)) (ITVar i) =
    case (M.lookup i m) of
      Just tyvar -> (e, TVar tyvar)
      Nothing ->
          let k = fromJustOrErr ("findK: " ++ ppReadable (e, i)) $ findK i e
              tyvar = TyVar i n (iToCK k)
              e' = E tm km eqs (PredEnv (n+1) (M.insert i tyvar m) s)
          in  (e', TVar tyvar)
convType e (ITCon i k s) = (e, TCon (TyCon i (Just (iToCK k)) s))
convType e (ITNum n) = (e, TCon (TyNum n noPosition))
convType e (ITStr s) = (e, TCon (TyStr s noPosition))

convTypes :: Env -> [IType] -> (Env, [Type])
convTypes e [] = (e, [])
convTypes e (t:ts) = let (e', t') = convType e t
                         (e'', ts') = convTypes e' ts
                     in  (e'', t':ts')

addPred :: SymTab -> Env -> IType -> PredEnv
addPred symt e@(E _ _ _ ps) t =
    let
        res =
            case (splitITAp t) of
              (ITCon i _ _, as) | (Just cls) <- findSClass symt (CTypeclass i)
                -> let (e', as') = convTypes e as
                   in  Just (e', IsIn cls as')
              _ -> Nothing
    in
        case res of
          Just (E _ _ _ (PredEnv n m s), new_pred) ->
              PredEnv n m (S.insert new_pred s)
          Nothing -> ps

------
