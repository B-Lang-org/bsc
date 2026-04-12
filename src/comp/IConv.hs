{-# LANGUAGE RankNTypes, ScopedTypeVariables, PatternGuards #-}
module IConv(
             iConvPackage, iConvT, iConvExpr, iConvSc, iConvDef,
             lookupSelType
            ) where

import Data.List(union, findIndex)
import Data.Maybe(catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as List

import Util(fromJustOrErr)
import qualified SCC(tsort,Graph)
--import Util(findDup,traces)
--import Util(trace_answer)
import FStringCompat(getFString)
import PPrint(ppReadable, ppString)
import Error(internalError, ErrorHandle)
import Flags(Flags)
import Position
import CSyntax
import CSyntaxTypes
import CFreeVars(getFVDl)
import Id
import PreStrings(fsTilde)
import PreIds

import Scheme
import Assump
import Pred
import SymTab
import Type(tPrimPair, tBit, HasKind(..))
import CType(cTVarKind, typeclassId, cTVarNum)
import VModInfo(mkVModInfo, VName(..), VFieldInfo(..))
import Type(tString, fn, tName, tAttributes)
import TCMisc(expandSynN)
import ISyntax
import ISyntaxSubst
import ISyntaxUtil
import Undefined
import Prim
import Pragma(CSchedulePragma, Pragma(..))
import IConvLet(docycles, reorderDs, unpoly)

-- import Debug.Trace

-- XXX consider creating an IConv state monad to store the various state
-- XXX that's passed around (read-only state like ErrorHandle, Flags, SymTab
-- XXX and possibly writeable state like the Env and scope variables)

type Env a = M.Map Id (IExpr a)

iConvPackage :: ErrorHandle -> Flags -> SymTab -> CPackage -> IO (IPackage a)
iConvPackage errh flags r (CPackage pi _ _ _ _ ds _) =
    return (IPackage pi [] ps ds')
  where ds' = concatMap (iConvD errh flags pi r env pvs) ds
        env = M.fromList ([(i, ICon i (ICDef t e)) | IDef i t e _ <- ds'])
        pvs = map IVar tmpVarIds
        ps = [ qualP p | CPragma p <- ds ]
        qualP (Pproperties i ps) = Pproperties (qualId pi i) ps
        qualP (Pnoinline is)     = Pnoinline (map (qualId pi) is)


iConvDef :: ErrorHandle -> Flags -> SymTab -> IPackage a -> CDefn -> IDef a
iConvDef errh flags r (IPackage pi _ _ ds) def =
    let env = M.fromList ([(i, ICon i (ICDef t e)) | IDef i t e _ <- ds])
        pvs = map IVar tmpVarIds
    in  case iConvD errh flags pi r env pvs def of
        [d] -> d
        ds -> internalError ("iConvDef " ++ ppReadable ds ++ ppReadable def)

iConvVar :: Flags -> SymTab -> Env a -> Id -> IExpr a
iConvVar flags r env i =
        --trace ("lookup " ++ ppReadable i ++ show env) $
        case M.lookup i env of
        Just (IVar i') -> IVar (setIdPosition (getIdPosition i) i')
        Just e  -> e
        Nothing ->
                case findVar r i of
                Just (VarInfo VarPrim (_ :>: sc) _ _) -> ICon i (ICPrim (iConvSc flags r sc) (toPrim i))
                Just (VarInfo (VarForg name mps) (_ :>: sc) _ _) ->
                        let t = iConvSc flags r sc
                            ops' = case mps of
                                   Just (ips, [op]) -> Just (zip ips (repeat 0), [(op, 0)])        -- XXX a hack for single output
                                   Just (ips, ops) -> Just (addSizes ips ops [] t)
                                   Nothing -> Nothing
                            addSizes (i:is) ops ins (ITAp (ITAp arr (ITAp bit (ITNum n))) r) | arr == itArrow && bit == itBit =
                                addSizes is ops ((i, n):ins) r
                            addSizes [] ops ins t = (reverse ins, zip ops (flatPairs t))
                            addSizes is ops ins t = internalError ("addSizes mismatch: " ++ ppReadable (is, ops, ins, t))
                            flatPairs (ITAp bit (ITNum n)) | bit == itBit = [n]
                            flatPairs (ITAp (ITAp pair a) b) = flatPairs a ++ flatPairs b
                            flatPairs it = internalError
                                           ("IConv.iConvVar.flatPairs: " ++
                                            show it)
                        in  ICon i (ICForeign t name False ops' Nothing)
                Just (VarInfo VarMeth (_ :>: Forall _ ((pp:_) :=> _)) _ _) ->
                    let (IsIn cl _) = removePredPositions pp
                    in iConvField flags r (typeclassId $ name cl) i
                Just (VarInfo VarDefn (_ :>: sc) _ _) ->
                    let t = iConvSc flags r sc
                    in  -- XXX should we use an error for the value
                        -- XXX so that it isn't silently used?
                        -- XXX (see similar code in GenBin)
                        ICon i (ICDef t (icUndetAt (getIdPosition i) t UNoMatch))
                _ -> IVar i

-- XXX is this really worthwhile now?
iConvTask :: SymTab -> Id -> IType -> IExpr a
iConvTask r i it =
   case findVar r i of
        -- only care about name - no "port-magic" for $display and friends
        Just (VarInfo (VarForg name _) _ _ _) ->
            -- trace("iConvTask: " ++ ppReadable it) $
            (ICon i (ICForeign it name False Nothing Nothing))
        Just x  -> internalError ("iConvTask: foreign function info for " ++
                            (show i) ++ " not expected.\n" ++ ppReadable x )
        Nothing -> internalError ("iConvTask: foreign function info for " ++
                            (show i) ++ " not found.\n" ++ ppReadable r )


addVar :: Id -> IExpr a -> Env a -> Env a
addVar i e t =
        --trace ("add " ++ ppReadable (i,e)) $
        M.insert i e t

type IPVars a = [IExpr a]

-----

iConvD :: ErrorHandle -> Flags -> Id -> SymTab -> Env a -> IPVars a ->
          CDefn -> [IDef a]
iConvD errh flags pi r env pvs (CValueSign (CDefT i vs qt cs)) =
    case iConvVS errh flags r env pvs i vs qt cs of
        (i, t, e) -> [IDef (qualId' pi i) t e [] ]
        -- ^ start out with no DefProps; they will be added in IExpand
iConvD errh flags pi r env pvs (CValueSign (CDef i qt cs)) =
    internalError "iConvD"
iConvD _ _ _ _ _ _ _ = []

-- only qualify non-instance names
qualId' :: Id -> Id -> Id
qualId' pi i = if tilde `elem` getIdString i then i else qualId pi i
  where tilde = case getFString fsTilde of
                  [c] -> c
                  _ -> internalError "IConv.qualId': unexpected tilde string"

iConvVS :: ErrorHandle
           -> Flags
           -> SymTab
           -> Env a
           -> IPVars a
           -> Id
           -> [TyVar]
           -> CQType
           -> [CClause]
           -> (Id, IType, IExpr a)
iConvVS errh flags r env pvs i vs (CQType _ t) cs =
        let t' = iConvT flags r t
            t'' = foldr (\ (TyVar i _ k) t -> ITForAll i (iConvK k) t) t' vs
            e' = foldr (\ (TyVar i _ k) e -> ILAM i (iConvK k) e) (iConvCs errh flags r env pvs t' cs) vs
        in  --trace ("iConvCs: " ++ ppReadable vs)
            (i, t'', e')

iConvT :: Flags -> SymTab -> Type -> IType
iConvT flags s t = iConvT' (expandSynN flags s t)

iConvT' :: Type -> IType
iConvT' (TVar (TyVar i _ _)) = ITVar i
iConvT' (TCon (TyCon i (Just k) s)) = ITCon i (iConvK k) s
iConvT' (TCon (TyNum n _)) = ITNum n
iConvT' (TCon (TyStr s _)) = ITStr s
iConvT' (TAp t1 t2) = normITAp (iConvT' t1) (iConvT' t2)
iConvT' t = internalError("iConvT': " ++ ppReadable t)

iConvK :: Kind -> IKind
iConvK KStar = IKStar
iConvK KNum = IKNum
iConvK KStr = IKStr
iConvK (Kfun k1 k2) = IKFun (iConvK k1) (iConvK k2)
iConvK (KVar _) = internalError "iConvK"

-- Given a list of triples:
-- * a value
-- * its type
-- * the pattern that is matching against that value
-- where the value is a type variable when converting clauses (the arg)
-- and the expr of "pat <- e" when used in a guard,
-- returns back a triple:
-- * a boolean expression indicating when the pattern matches
-- * list of variable bindings from the pattern
-- * the environment updated with the variable bindings
--
iConvPs :: Flags -> SymTab -> Env a -> [(IExpr a, IType, CPat)] ->
           (IExpr a, [(Id, IType, IExpr a)], Env a)
iConvPs flags r env vtps = iConvPs' flags r env id [] (length vtps) vtps

iConvPs' :: Flags -> SymTab -> Env a ->
            (IExpr a -> IExpr a) -> [(Id, IType, IExpr a)] -> Int ->
            [(IExpr a, IType, CPat)] -> (IExpr a, [(Id, IType, IExpr a)], Env a)
iConvPs' flags r env cond bs n [] = (cond iTrue, bs, env)

iConvPs' flags r env cond bs n ((v, _, CPConTs ti i ots [pat]) : ps) =
        --trace (ppReadable (out, outty, conty)) $
        iConvPs' flags r env (cond . isTest) bs n ((out, argType ty, pat) : ps)
  where ts = map (iConvT flags r) ots
        (conty, cti) = lookupConType flags ti i r
        mkOutTy (ITAp (ITAp arr a) r) = ITAp (ITAp arr r) a
        mkOutTy _ = internalError "IConv.iConvPs' mkOutTy"
        mkIsTy (ITAp (ITAp arr a) r) = ITAp (ITAp arr r) itBit1
        mkIsTy _ = internalError "IConv.iConvPs' mkIsTy"
        outty = underForAll conty (length ts) mkOutTy
        isty  = underForAll conty (length ts) mkIsTy
        out = IAps (ICon i (ICOut outty cti)) ts [v]
        is  = IAps (ICon i (ICIs  isty  cti)) ts [v]
        isTest = if numCon cti == 1 then id else (is `ieAnd`)
        ty = iInst conty ts
iConvPs' flags r env cond bs n ((v, _, CPConTs _ _ _ _) : ps) =
    internalError "iConvPs' CPConTs"
iConvPs' flags r env cond bs n ((v, _, CPCon i _) : ps) =
    internalError "iConvPs' CPCon"

iConvPs' flags r env cond bs n ((v, t, CPstruct _ _ fs) : ps) =
    iConvPs' flags r env cond bs (n+length fs) (foldr addP ps fs)
  where (ti, ts) = splitITApCon t
        addP (f, p) ps =
                let sel = iConvField flags r ti f
                    selty = case sel of
                              (ICon _ (ICSel t _ _)) -> t
                              _ -> internalError "IConv.iConvPs' CPstruct: selty"
                    ty = iInst selty ts
                in  --trace ("iConvPs' " ++ ppReadable (sel, selty, ts, ty)) $
                    (IAps sel ts [v], resType ty, p) : ps

iConvPs' flags r env cond bs n ((v, t, CPVar x) : ps) =
    iConvPs' flags r (addVar x v env) cond ((x,t,v):bs) n ps
iConvPs' flags r env cond bs n ((v, t, CPAs x p) : ps) =
    iConvPs' flags r (addVar x v env) cond ((x,t,v):bs) n ((v, t, p):ps)
iConvPs' flags r env cond bs n ((v, t, CPAny p) : ps) =
    iConvPs' flags r env cond bs n ps
-- We don't handle CPLit or CPMixedLit here because TCheck removes literals
-- and replaces them with a variable and a guard
iConvPs' flags r env cond bs n _ = internalError ("iConvPs'")

iConvCs :: ErrorHandle -> Flags -> SymTab -> Env a ->
           IPVars a -> IType -> [CClause] -> IExpr a
iConvCs errh flags r env pvs t cs@(CClause ps _ _ : _) =
    foldr (uncurry ILam) (iConvCs' errh flags r env pos pvs' (map (IVar . fst) vts) ts rt cs) vts
  where getArgs (_:ps) (ITAp (ITAp arr a) r) | arr == itArrow = a : getArgs ps r
        getArgs (_:_) t = internalError ("getArgs: " ++ ppReadable t)
        getArgs [] rt = [rt]
        tsrt = getArgs ps t
        ts = init tsrt
        rt = last tsrt
        pickVar (CPVar v) _ = v
        pickVar _ (IVar v) = v
        pickVar p v = internalError ("iConvCs.pickVar: " ++ show (p, v))
        vts = zipWith3 (\ p iv t -> (pickVar p iv, t)) ps pvs ts
        pvs' = drop (length ps) pvs
        pos = getPosition ps
iConvCs errh flags r env pvs t [] = internalError "IConv.iConvCs: []"

iConvCs' :: ErrorHandle -> Flags -> SymTab -> Env a
         -> Position -> IPVars a -> [IExpr a] -> [IType] -> IType -> [CClause]
         -> IExpr a
iConvCs' errh flags r env pos pvs (v:vs) (t_v:t_vs) t [] =
    -- take the position of the first scrutinee if you can
    buildUndefNoMatchPos flags r env (v,t_v) t
iConvCs' errh flags r env pos pvs _ _ t [] =
    -- take the position of the case if you can't
    buildUndef flags r env pos UNoMatch t
iConvCs' errh flags r env pos pvs vs ts t (c:cs) =
    ieIf t cond rhs (iConvCs' errh flags r env pos pvs vs ts t cs)
  where (cond, rhs) = iConvC errh flags r env pvs vs ts c

iConvC :: ErrorHandle -> Flags -> SymTab -> Env a ->
          IPVars a -> [IExpr a] -> [IType] -> CClause -> (IExpr a, IExpr a)
iConvC errh flags r env pvs vs ts (CClause ps qs e) =
    let (p1, _, env') = iConvPs flags r env (zip3 vs ts ps)
        (p2, bindFn, env'') = iConvQs errh flags r env' pvs qs
    in  (ieAnd p1 p2, bindFn $ iConvE errh flags r env'' pvs e)

-- Given:
-- * a list of guards
-- returns a triple:
-- * a boolean for when the guards match
-- * the bindings for the pattern variables, expressed as let blocks
--   (we used to return the environment with these bindings,
--    but that doesn't work)
-- * the environment updated to refer to those bound variable names
--   (rather than inline the expressions they are bound to)
--
-- Note: This used to consume "pvs" to create a new binding for when
-- the guard "C v <- e" is encountered.  The intention was to create
-- the syntax "let a = e" and then add "v = selFn a" to the environment,
-- which would properly capture the scope of free vars in "e".  However,
-- it was actually adding "v = selFn e" and adding "let a = e" to the
-- wrong place.  This opened up Bug 1753, which was fixed by returning
-- the bindings that need to be added to the syntax.  However, it also
-- changed what the bindings were; we go ahead and create "let v = selFn e"
-- and never declare "a", which has the advantage of allowing "v" to be
-- preserved if it's a name that has meaning to the user (but is there an
-- efficiency trade-off?).
--
iConvQs :: ErrorHandle -> Flags -> SymTab -> Env a ->
           IPVars a -> [CQual] -> (IExpr a, (IExpr a -> IExpr a), Env a)
iConvQs errh flags r env pvs qs = iConvQs' errh flags r env pvs id [] qs

iConvQs' :: ErrorHandle -> Flags -> SymTab -> Env a ->
            IPVars a -> (IExpr a -> IExpr a) -> [(Id, IType, IExpr a)] ->
            [CQual] -> (IExpr a, (IExpr a -> IExpr a), Env a)
iConvQs' errh flags r env pvs cond bs [] =
    let -- create let bindings
        -- (use iLetSimp, to inline names that we don't need to keep;
        -- it's OK, because inlining will rename free vars to avoid capture)
        bindFoldFn e_body (i,t,e) = iLetSimp i t e e_body
        eFn e = foldl bindFoldFn e bs
        -- now update the env to use those bindings rather than
        -- inlining the expressions (which gets the scoping wrong)
        envFoldFn accum_env (i,_,_) = addVar i (IVar i) accum_env
        env' = foldl envFoldFn env bs
    in  (cond iTrue, eFn, env')
iConvQs' errh flags r env pvs cond bs (CQFilter e:qs) =
    let cond' = cond . (toBit (iConvE errh flags r env pvs e) `ieAnd`)
    in  iConvQs' errh flags r env pvs cond' bs qs
iConvQs' errh flags r env pvs cond bs (CQGen ct p e:qs) =
    let e' = iConvE errh flags r env pvs e
        t = iConvT flags r ct
        -- get the updated env, because other guards might refer to the
        -- bound pattern variables; but we overwrite the bs before
        -- returning the env (see the base case above)
        (cond2, bs2, env') = iConvPs flags r env [(e', t, p)]
        new_cond = cond . (cond2 `ieAnd`)
        new_bs = bs2 ++ bs
    in  iConvQs' errh flags r env' pvs new_cond new_bs qs

-- convert definitions in a sequential let
iConvLetSeq :: ErrorHandle -> Flags -> SymTab -> Env a ->
               IPVars a -> [CDefl] -> (Env a, [(Id, IType, IExpr a)])
iConvLetSeq errh flags symtab env ipvars [] = (env, [])
iConvLetSeq errh flags symtab env ipvars
        (CLValueSign (CDefT name genvars qualtype clauses) quals : rest_defs) =
    let env_with_def = addVar name (IVar name) env
        conv_clauses env' ipvars' = -- env and ipvars modified by iAddWhen
            iConvVS errh flags symtab env' ipvars' name genvars qualtype clauses
        conv_clauses_quals = iAddWhen errh flags symtab env ipvars quals conv_clauses
        (env_final, conv_rest) =
            iConvLetSeq errh flags symtab env_with_def ipvars rest_defs
    in  (env_final, conv_clauses_quals : conv_rest)
iConvLetSeq _ _ _ _ _ _ = internalError "iConvLetSeq"

-- convert definitions in a recursive let
iConvLet :: forall a .
            ErrorHandle -> Flags -> SymTab -> Env a -> IPVars a -> [CDefl] ->
            (Env a, [(Id, IType, IExpr a)])
iConvLet errh flags r env pvs ds = answer
  where answer = case loop_test of
                   Left cycles -> -- trace "inloop" $
                                  deal_with_cycles cycles
                   Right _ -> -- trace ("iConvLet: " ++ ppReadable ds ++ "\n\n\n" ++ ppReadable ites ++ "/iconvLet") $
                              (env', ites)
        ites = map f ds'
               where
                 f (CLValueSign (CDefT i vs qt cs) me) =
                     iAddWhen errh flags r env' pvs me ite
                     where
                       ite env pvs = iConvVS errh flags r env pvs i vs qt cs
                 f _ = internalError "iConvLet.ites.f"
        d_ids = [ i | (CLValueSign (CDefT i _ _ _) _) <- ds ]
        env' = let addFn i e = addVar i (IVar i) e
               in  foldr addFn env d_ids
        is :: S.Set Id
        is = S.fromList d_ids
        graph :: SCC.Graph Id -- [(Id,[Id])]
        graph = [(i, local_is) |
                   d@(CLValueSign (CDefT i _ _ _) _) <- ds,
                   -- self-recursion is caught by unrec, below
                   let local_is =
                         filter ((/=) i)
                           (S.toList
                              ((snd (getFVDl d)) `S.intersection` is))]
        ds' :: [CDefl]
        ds' = case loop_test of
                Left cycles -> internalError "iConvLet.cycles"
                Right is' -> map unrec (reorderDs ds is')
        loop_test :: Either [[Id]] [Id]
        loop_test = SCC.tsort graph
        unrec :: CDefl -> CDefl
        unrec d@(CLValueSign (CDefT i vs qt@(CQType ctx ft) cs) me) =
           if S.member i (snd (getFVDl d)) then
           let answer =
                let prim_fix_pos = CVar (idPrimFix (getPosition i))
                    rlet = Cletrec [CLValueSign funbind []] (CApply (CTApply prim_fix_pos [ft]) [CVar _f])
                    _f = id_fun
                    pi = CPVar i
                    funbind = CDefT _f [] (CQType ctx (ft `fn` ft)) [CClause (pi:ps) qs (unpoly i e) | CClause ps qs e <- cs]
                in  CLValueSign (CDefT i vs qt [CClause [] [] rlet]) me
               in -- trace ("unrec=====\n" ++ (ppReadable d) ++ (show d) ++
                  -- {- "\nsymtab=\n" ++ (ppReadable r) ++ -}
                  -- "\n\nanswer=\n" ++ (ppReadable answer) ++ "====unrec") $
                  answer
            else
                d
        unrec d = internalError("IConv.iConvLet.unrec " ++ (ppReadable d))

        deal_with_cycles cycle_nodes =
            let
                all_nodes :: [Id]
                all_nodes = map fst graph
                non_cycle :: [CDefl]
                non_cycle = reorderDs ds $
                            all_nodes List.\\ (concat cycle_nodes)
            in iConvLet errh flags r env pvs
                   (non_cycle ++ (docycles errh ds cycle_nodes))

iAddWhen :: ErrorHandle -> Flags -> SymTab -> Env a
         -> IPVars a -> [CQual] -> (Env a -> IPVars a -> (Id, IType, IExpr a))
         -> (Id, IType, IExpr a)
iAddWhen errh flags r env pvs [] ite = ite env pvs
iAddWhen errh flags r env pvs qs ite =
    let (p, bindFn, env') = iConvQs errh flags r env pvs qs
        underLAM (ITForAll _ _ t) (ILAM v k e) vks f = underLAM t e ((v,k):vks) f
        underLAM t                e            vks f = foldl (\ e (v,k) -> ILAM v k e) (f t e) vks
    in  case ite env' pvs of
        (i, t, e') -> (i, t, underLAM t e' [] $ \ t e -> iAps icPrimWhen [t] [p, bindFn e])

-- external interface for converting expressions
iConvExpr :: ErrorHandle -> Flags -> SymTab -> Env a -> CExpr -> IExpr a
iConvExpr errh flags r env ce = iConvE errh flags r env (map IVar tmpVarIds) ce

iConvE :: ErrorHandle -> Flags -> SymTab -> Env a -> IPVars a ->
          CExpr -> IExpr a
-- CLam
iConvE errh flags r env pvs (Cletrec ds e) =
        let (env', ites) = iConvLet errh flags r env pvs ds
        in  foldr (uncurry3 iLetSimp) (iConvE errh flags r env' pvs e) ites
iConvE errh flags r env pvs (Cletseq defs body) =
        let (env', ites) = iConvLetSeq errh flags r env pvs defs
        in  foldr (uncurry3 iLetSimp) (iConvE errh flags r env' pvs body) ites
iConvE errh flags r env pvs (CSelectT ti i) = iConvField flags r ti i
iConvE errh flags r env pvs (CApply (CTApply (CVar i) ts) (e:es)) | isField =
        let (ts1, ts2) = splitAt n (map (iConvT flags r) ts)
        in  iAps (IAps ie ts1 [iConvE errh flags r env pvs e]) ts2 (map (iConvE errh flags r env pvs) es)
  where ie = iConvVar flags r env i
        (isField, n) = case ie of
                        ICon _ (ICSel t _ _) -> (True, countForall t)
                        _ -> (False, 0)
iConvE errh flags r env pvs (CConT ti c es) =
        let (t, cti) = lookupConType flags ti c r
        in  iAps (ICon c (ICCon t cti)) [] (map (iConvE errh flags r env pvs) es)
-- Ccase
iConvE errh flags r env pvs (CStructT ct []) = con
  where con = iAPs ict itvs
        ict = ICon ti (ICTuple tupty [])
        tupty = foldr (\tv t -> ITForAll (tv_name tv) (iConvK $ tv_kind tv) t) it tvs
        it = iConvT flags r ct
        tvs = tv ct
        itvs = map (iConvT flags r. TVar) tvs
        ti = fst $ splitITApCon it
iConvE errh flags r env pvs eee@(CStructT ct fs@((f,_):_)) =
 --trace (ppReadable (eee, map fst fs)) $
 --trace (ppReadable (map (\ (f,_) -> lookupSelType flags ti f r) fs)) $
 iAps con [] (map (iConvE errh flags r env pvs . snd) fs)
  where con = iAPs ict ts
        ict = ICon ti (ICTuple tupty (map fst fs))
        tupty = foldr (\ (v, k) t -> ITForAll v k t) (foldr itFun st fts) (zip vs ks)
        fts = map (\ (f,_) -> resType (iInst (lookupSelType flags ti f r) tvs)) fs
        (ti, ts) = splitITApCon (iConvT flags r ct)
        n = length ts
        vs = take n tmpTyVarIds
        tvs = map ITVar vs
        ks = getKs n fty
        fty = lookupSelType flags ti f r
        st = argType (iInst fty tvs)
-- Get rid of dictionary argument to primConcat & co
iConvE errh flags r env pvs (CApply (CTApply (CVar i) ts) (_: es))
    | (Just f) <- lookup i dropDicts =
        IAps f (map (iConvT flags r) ts) (map (iConvE errh flags r env pvs) es)
-- XXX should get rid of primSplitFst & primSplitSnd
iConvE errh flags r env pvs (CApply (CTApply (CVar sfst) [t1,t2,t3]) [_, e])
    | sfst == idPrimSplitFst =
        let k = iConvT flags r t1
            m = iConvT flags r t2
            n = iConvT flags r t3
        in  IAps (icSelect noPosition) [k, m, n] [iConvE errh flags r env pvs e]
iConvE errh flags r env pvs (CApply (CTApply (CVar ssnd) [t1,t2,t3]) [_, e])
    | ssnd == idPrimSplitSnd =
        let k = iConvT flags r t2
            m = mkNumConT 0
            n = iConvT flags r t3
        in  IAps (icSelect noPosition) [k, m, n] [iConvE errh flags r env pvs e]
iConvE errh flags r env pvs (CApply (CTApply (CVar splt) ts@[n, m, k]) es@[d, e])
    | splt == idPrimSplit =
        let fstE = CApply (CTApply (CVar idPrimSplitFst) ts) es
            sndE = CApply (CTApply (CVar idPrimSplitSnd) ts) es
            ct = TAp (TAp tPrimPair (TAp tBit n)) (TAp tBit m)
            e = CStructT ct [(idPrimFst, fstE), (idPrimSnd, sndE)]
        in  iConvE errh flags r env pvs e

iConvE errh flags r env pvs (CApply (CVar gn) [CVar name]) | gn == idPrimGetName =
  ICon gn (ICName { iConType = iConvT flags r tName, iName = name })

iConvE errh flags r env pvs (CAny pos uk) =
  internalError ("iConvE: CAny " ++ prPosition pos)
iConvE errh flags r env pvs (CAnyT pos uk t) =
  buildUndef flags r env pos uk (iConvT flags r t)

iConvE errh flags r env pvs (CVar i) = iConvVar flags r env i

iConvE errh flags r env pvs (CTaskApplyT (CVar taskid) t es) =
  let -- find unsimplified numeric types (e.g. SizeOf a)
      -- so that they can be carved out for the evaluator to fix
      badNumAps ap@(TAp f a) | kind ap == KNum = S.singleton ap
                             | otherwise = badNumAps f `S.union` badNumAps a
      badNumAps _ = S.empty
      badNums = S.toList (badNumAps t)

      -- fix the problem by passing in the bad numeric types
      -- as explicit type arguments (which requires rewriting the original type)
      numVarNames = take (length badNums) tmpTyNumIds
      numVarTypes = map cTVarNum numVarNames
      fixupMap = M.fromList (zip badNums numVarTypes)
      fixupType ap@(TAp f a) | Just ap' <- M.lookup ap fixupMap = ap'
                             | otherwise = TAp (fixupType f) (fixupType a)
      fixupType t0           = t0

      t_fix = fixupType t
      it_fix = foldr (\v t_n -> ITForAll v IKNum t_n) (iConvT flags r t_fix) numVarNames
      it_args = map (iConvT flags r) badNums in

     iAps (iConvTask r taskid it_fix) it_args (map (iConvE errh flags r env pvs) es)

iConvE errh flags r env pvs (CApply e es) =
  iAps (iConvE errh flags r env pvs e) [] (map (iConvE errh flags r env pvs) es)
iConvE errh flags r env pvs (CLitT t (CLiteral pos l)) =
  iConvLit l pos (iConvT flags r t)
-- iConvE errh flags r env pvs (CLit (CLiteral pos l@(LString s))) = iConvLit l pos (iConvT flags r tString)
-- CBinOp, CHasType, Cif, Csub
iConvE errh flags r env pvs (CTApply e ts) =
  iAPs (iConvE errh flags r env pvs e) (map (iConvT flags r) ts)
iConvE errh flags r env pvs (Crules sps rs) =
    let rs' = concatMap (flattenRules [] [] []) rs
        rs'' = map (iConvR errh flags r env pvs) rs'
        rs_final = foldr ieJoinR icNoRules rs''
        sps_final = iConvSchedulePragmas sps
    in  iAps icAddSchedPragmas [] [sps_final, rs_final]
iConvE errh flags r env pvs e@(CmoduleVerilogT ty name ui clks rst args meths sch ps) =
        let vinf = -- traces( "=== iConvE: " ++ show name ++ " " ++ show e ) $
                   mkVModInfo
                    (VName "???")
                    clks
                    rst
                    (map fst args)
                    meths sch ps
            es' = map (iConvE errh flags r env pvs . snd) args
            getMethodName (Method { vf_name = i }) = i
            getMethodName (Clock i) = i
            getMethodName (Reset i) = i
            getMethodName (Inout { vf_name = i }) = i
            tss = map (tail . itSplit . getMethodType flags r ti ts . getMethodName) meths
            ty' = iConvT flags r ty
            ty'' = case dropA es' ty' of
                     ITAp _ t -> t
                     _ -> internalError "IConv.iConvE CmoduleVerilogT: dropA result"
                where dropA [] t = t
                      dropA (_:es) (ITAp _ t) = dropA es t
                      dropA _ _ = internalError "IConv.iConvE.dropA"
            (ti, ts) = splitITApCon ty''
            name' = iConvE errh flags r env pvs name
        in  iAps (ICon (dummyId (getPosition e))
                     (ICVerilog { iConType = itString `itFun` ty',
                                  isUserImport = ui,
                                  vInfo = vinf,
                                  vMethTs = tss })) [] (name' : es')

iConvE errh flags r enc pvs e@(CForeignFuncCT i prim_ty) =
    let name = getIdString i
        ty' = iConvT flags r prim_ty
    in  ICon i (ICForeign ty' name True Nothing Nothing)

iConvE errh flags r env pvs (Cattributes pps) =
    ICon (dummyId (getPosition (map fst pps)))
         (ICAttrib { iConType = iConvT flags r tAttributes, iAttributes = pps })
iConvE errh flags r env pvs e = internalError ("IConv.iConvE:" ++ ppReadable e)

getMethodType :: Flags -> SymTab -> Id -> [IType] -> Id -> IType
getMethodType flags r ti ts m = iInst selty ts
  where sel = iConvField flags r ti m
        selty = case sel of
                  (ICon _ (ICSel t _ _)) -> t
                  _ -> internalError "IConv.getMethodType: selty"

iConvR :: ErrorHandle -> Flags -> SymTab -> Env a ->
          IPVars a -> CRule -> IExpr a
iConvR errh flags r env pvs rule@(CRule rps i qs a) =
    let (p, bindFn, env') = iConvQs errh flags r env pvs qs
        a' = bindFn $ iConvE errh flags r env' pvs a
        s = case i of Nothing -> iMkStringAt (getPosition rule) ""
                      Just i -> iConvE errh flags r env pvs i
        eas = iConvRulePragmas rps
    in  iAps icRule [] [s, eas, p, a']
iConvR errh flags r env pvs rule =
    internalError ("IConv.iConvR: nested rule: " ++ show rule)

iConvRulePragmas :: [RulePragma] -> IExpr a
iConvRulePragmas as = ICon (dummyId noPosition) (ICRuleAssert { iConType = itBit0, iAsserts = as })

iConvSchedulePragmas :: [CSchedulePragma] -> IExpr a
iConvSchedulePragmas sps = ICon (dummyId noPosition) (ICSchedPragmas { iConType = itSchedPragma, iPragmas = sps })

flattenRules :: [RulePragma] -> [Maybe CExpr] -> [CQual] -> CRule -> [CRule]
flattenRules rps is qs (CRuleNest rps' i qs' rs) =
    concatMap (flattenRules (rps `union` rps') (i:is) (qs++qs')) rs
flattenRules rps is qs (CRule rps' l qs' a) =
    [CRule (rps `union` rps') (joinRuleIds (catMaybes (l:is))) (qs++qs') a]

joinRuleIds :: [CExpr] -> Maybe CExpr
joinRuleIds [] = Nothing
joinRuleIds is =
    Just (foldr1 (\ i1 i2 -> ruleStrConcat i2 (ruleStrConcat str_ i1)) is)

-- use idPrimStringConcatAt so that the expression has a good position.
-- for rules, the best position is the second string, since it's the most
-- specific to the rule
ruleStrConcat :: CExpr -> CExpr -> CExpr
ruleStrConcat e1 e2 =
    let pos = getPosition e2
    in  cVApply (idPrimStringConcatAt pos) [e1, e2]

str_ :: CExpr
str_ = CLitT tString (CLiteral noPosition (LString "_"))

dropDicts :: [(Id, IExpr a)]
dropDicts = [(idPrimConcat, icPrimConcat),
             (idPrimZeroExt, icPrimZeroExt),
             (idPrimSignExt, icPrimSignExt),
             (idPrimTrunc, icPrimTrunc),
             (idPrimMul, icPrimMul)]

iConvLit :: Literal -> Position -> IType -> IExpr a
iConvLit (LInt i) pos t = ICon (setIdPosition pos idIntLit) (ICInt { iConType = t, iVal = i })
iConvLit (LReal r) pos t = ICon (setIdPosition pos idRealLit) (ICReal { iConType = t, iReal = r })
iConvLit (LString s) pos t = iMkStringAt pos s
iConvLit (LChar c) pos t = iMkCharAt pos c
iConvLit LPosition pos t = iMkPosition pos

-- converts implicit field extract functions to bit select.
iConvField :: Flags -> SymTab -> Id -> Id -> IExpr a
iConvField flags r ti i =
    case findType r ti of
      Just (TypeInfo _ _ _ (TIstruct _ fs) _) ->
          --trace ("iConvField " ++ ppReadable (i, ti, fs, elemIndex i fs)) $
          --trace ("iConvField " ++ ppReadable (i, lookupSelType flags ti i r)) $
          let fieldnum = fromJustOrErr "iConvField" (findIndex (qualEq i) fs)
          in  ICon i (ICSel (lookupSelType flags ti i r) (toInteger fieldnum) (toInteger (length fs)))
      tyi -> internalError ("iConvField: " ++ ppReadable (i, ti, tyi))

{-
--- XXX not very efficient
iTypeFieldTypeArity :: SymTab -> Id -> Id -> Int
iTypeFieldTypeArity r ti c =
        case findField r c of
        Just xs -> case [ n | (FieldInfo { fi_id = ti', fi_arity = n }) <- xs,
                              ti == ti'] of [n] -> n
        Nothing -> internalError ("iTypeFieldTypeArity: " ++ ppString c)
-}

lookupConType :: Flags -> Id -> Id -> SymTab -> (IType, ConTagInfo)
lookupConType flags ti c r =
        case findCon r c of
        Just xs -> let convs = [(iConvSc flags r sc, ci_taginfo ci)
                                | ci@ConInfo { ci_assump = (_ :>: sc) } <- xs,
                                qualEq ti (ci_id ci)]
                   in  case convs of
                       [x] -> x
                       _  -> internalError ("IConv.lookupConType: convs: " ++
                                            show convs)
        Nothing -> internalError ("lookupConType: " ++ ppString c)

lookupSelType :: Flags -> Id -> Id -> SymTab -> IType
lookupSelType flags ti c r =
        case findField r c of
        Just xs ->
            let scns = [(sc, n) | (FieldInfo { fi_id = ti',
                                               fi_arity = n,
                                               fi_assump = (_ :>: sc) }) <- xs,
                                  qualEq ti ti']
            in  case scns of
                        [(sc, n)] ->
                                --trace ("lookupSelType " ++ ppReadable (ti, c, n, iConvSc flags r sc)) $
                                moveForAll n ti (iConvSc flags r sc)
                        ys -> internalError ("lookupSelType: " ++ ppString (xs, (ti, c), ys))
        Nothing -> internalError ("lookupSelType: " ++ ppString c)

iConvSc :: Flags -> SymTab -> Scheme -> IType
iConvSc flags r (Forall ks qt) =
    foldr (uncurry ITForAll) (iConvT flags r (inst ts (qualToType qt))) (zip vs (map iConvK ks))
  where vs = tmpTyVarIds
        ts = zipWith cTVarKind vs ks
--iConvSc r t = internalError ("iConvSc: " ++ ppReadable t)

-- Turn a field (selector) type back to its true type
moveForAll :: Int -> Id -> IType -> IType
moveForAll 0 ti t =
        let (s, t') = find t
            find (ITAp (ITAp fn tia) t) | fn == itArrow && isTI tia = (tia, t)
            find (ITAp f a) = (tia, ITAp f a') where (tia, a') = find a
            find (ITForAll i k t) = (tia, ITForAll i k t') where (tia, t') = find t
            find t = internalError ("moveForAll.find " ++ ppReadable (ti, t))
            isTI (ITCon i _ _) = qualEq i ti
            isTI (ITAp f _) = isTI f
            isTI t = internalError ("moveForAll.isTI " ++ ppReadable (ti, t))
            --isTI _ = False
        in  itFun s t'
moveForAll n ti (ITForAll i k t) = ITForAll i k (moveForAll (n-1) ti t)
moveForAll n ti t = internalError ("moveForAll: " ++ ppReadable (n, ti, t))

---------

{-
splitCTAp :: CType -> (Id, [CType])
splitCTAp (TAp f a) = (c, a:as) where (c, as) = splitCTAp f
splitCTAp (TCon (TyCon i _ _)) = (i, [])
splitCTAp t = internalError ("splitCTAp " ++ ppReadable t)

getTFields :: CType -> [Id]
getTFields (TAp f _) = getTFields f
getTFields (TCon (TyCon _ _ (TIstruct _ fs))) = fs
getTFields t = internalError ("getTFields " ++ ppReadable t)
-}

splitITApCon :: IType -> (Id, [IType])
splitITApCon t = case (splitITAp t) of
                   (ITCon i _ _, as) -> (i, as)
                   _ -> internalError ("splitITApCon " ++ ppReadable t)

-- Get first argument to a (possibly quantified) function
argType :: IType -> IType
argType (ITAp (ITAp arr a) _) | arr == itArrow = a
argType (ITForAll _ _ t) = argType t        -- A hack...
argType t = internalError ("argType: " ++ ppReadable t)

-- Drop first argument to a (possibly quantified) function
resType :: IType -> IType
resType (ITAp (ITAp arr _) r) | arr == itArrow = r
resType (ITForAll i k t) = ITForAll i k (resType t) -- A hack...
resType t = internalError ("resType: " ++ ppReadable t)

iInst :: IType -> [IType] -> IType
iInst t [] = t
iInst (ITForAll i _ r) (t:ts) = iInst (tSubst i t r) ts
iInst t ts = internalError ("iInst: " ++ ppReadable (t, ts))

underForAll :: IType -> Int -> (IType -> IType) -> IType
underForAll t 0 f = f t
underForAll (ITForAll i k t) n f = ITForAll i k (underForAll t (n-1) f)
underForAll itype _ _ = internalError ("IConv.underForAll: " ++ show itype)

getKs :: Int -> IType -> [IKind]
getKs 0 _ = []
getKs n (ITForAll _ k t) = k : getKs (n-1) t
getKs _ itype = internalError ("IConv.getKs: " ++ show itype)

countForall :: IType -> Int
countForall (ITForAll _ _ t) = 1 + countForall t
countForall _ = 0

------

iLetSimp :: Id -> IType -> IExpr a -> IExpr a -> IExpr a
iLetSimp i _ e@(IVar _) b | not (isKeepId i) = eSubst i e b
{-
iLetSimp i t e b | onlyIAP b = iTypeBeta (eSubst i e b)
  where iTypeBeta (IAps f [t] []) = ap (iTypeBeta f) t
          where ap (ILAM i _ e) t = iTypeBeta (etSubst i t e)
                ap f t = iAP f t
        iTypeBeta (IAps f (t:ts) []) = iTypeBeta (IAps (iTypeBeta (IAps f [t] [])) ts [])
        iTypeBeta e = e
        onlyIAP (IAps e _ []) = onlyIAP e
        onlyIAP (IVar _) = True
        onlyIAP _ = False
-}
iLetSimp i t e b = iLet i t e b

---

buildUndef :: Flags -> SymTab -> Env a ->
              Position -> UndefKind -> IType -> IExpr a
buildUndef flags r env pos kind t =
    IAps p [t] [iMkPosition pos, iuKindToExpr kind]
  where p = iConvVar flags r env idBuildUndef

-- use the scrutinee's position to build the undefined value on a no-match
buildUndefNoMatchPos :: Flags -> SymTab -> Env a ->
                        (IExpr a, IType) -> IType -> IExpr a
buildUndefNoMatchPos flags r env (e, t_e) t =
    IAps bu [t] [IAps gp [t_e] [e], iuNoMatchExpr]
  where bu = iConvVar flags r env idBuildUndef
        gp = ICon idPrimGetEvalPosition (ICPrim itPrimGetPosition PrimGetEvalPosition)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f ~(x, y, z) = f x y z
