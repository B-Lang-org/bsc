module LiftDicts(liftDictsPkg) where

import Control.Applicative((<|>))
import Control.Monad(when, zipWithM)
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Debug.Trace(traceM)

import Error(ErrorHandle)
import ErrorUtil(internalError)
import Flags(Flags)
import IOUtil(progArgs)
import Util(mapSndM)

import CSyntax
import FStringCompat(FString)
import CFreeVars(getPV, getFVE, fvSetToFreeVars)
import CType
import Assump
import Pred
import Scheme
import Subst(mkSubst, Types(..))
import Id
import Position(Position, noPosition)
import PPrint
import PreIds
import SymTab
import IConv(iConvT, iConvK, iConvExpr)
import ISyntax
import ISyntaxUtil(icUndetAt)
import Undefined(UndefKind(..))

trace_lift_dicts :: Bool
trace_lift_dicts = "-trace-lift-dicts" `elem` progArgs

-- =====
-- Dictionary lifting
--
-- Lift the (monomorphic, fully-applied) typeclass dictionaries that
-- the typechecker bound inside each definition to package top level,
-- so that one dictionary value is built and shared per package rather
-- than rebuilt at every use.
--
-- Lifted dictionaries are constructed directly as ISyntax IDefs: when
-- a dictionary is lifted, its type and evidence are converted with the
-- production IConv machinery, and the pass accumulates (id, interned
-- IType, IExpr evidence).  The CSyntax rewrite only ever introduces
-- references (CVar lifted_id); the definitions themselves never
-- reappear as CSyntax.  The accumulated IDefs are appended to the
-- converted package by iConvPackage (which also extends its conversion
-- environment with them, so the CVar references resolve), and from
-- there they flow through fixupDefs and into the .bo like any other
-- top-level definition.
--
-- Deduplication within the package is by interned type AND structural
-- evidence: candidates are bucketed in a map keyed by the interned
-- IType (position-insensitive cmpT order), and a candidate is reused
-- only when its converted evidence is structurally equal (IExpr
-- equality: Ids by name, types by interned cmpT).  Two dictionaries of
-- the same type built from different evidence -- possible with orphan
-- or incoherent instances -- always stay distinct.  Cross-package
-- deduplication (FixupDefs) relies on the same structural discipline.

liftDictsPkg :: ErrorHandle -> Flags -> SymTab -> CPackage
             -> (CPackage, [IDef a])
liftDictsPkg errh flags symt pkg@(CPackage mi exps imps impsigs fixs ds includes)
  = (CPackage mi exps imps impsigs fixs ds' includes, reverse (liftedDefs s'))
  where s0 = initLState errh flags symt pkg
        (ds', s') = runState (liftDicts S.empty M.empty ds) s0

data LState a = LState {
  errHandle :: ErrorHandle,
  flags :: Flags,
  -- source of unique numbers to append to top-level dict names
  dictNo :: !Int,
  -- The lifted-dictionary pool: interned type -> lifted candidates, in
  -- lifting order.  A dictionary is reused only on a structural match
  -- of its converted evidence (see the module note above).
  dictPool :: M.Map IType [(Id, IExpr a)],
  -- The lifted definitions, most recent first (reversed at the end, so
  -- the emitted order is lifting order and thus deterministic)
  liftedDefs :: [IDef a],
  -- CSyntax types of the lifted dictionaries, for the CSyntax-side
  -- analysis (getTopNameInfo) of later dictionary expressions
  liftedTypes :: M.Map Id CType,
  -- Conversion environment for lifting: maps every id a lifted
  -- evidence expression may reference -- previously lifted
  -- dictionaries and the package's converted-instance definitions --
  -- to a reference node carrying its interned type.  Everything else
  -- resolves through the symbol table inside IConv, exactly as
  -- references to imported definitions do.  The bodies here are
  -- placeholders; fixupDefs later ties all references to the real
  -- definitions.
  convEnv :: M.Map Id (IExpr a),
  -- Information about instances that do not appear in the symbol table.
  -- These are converted instance definitions that were added by convinst
  -- but never incorporated into the symbol table.
  localInstInfo :: M.Map Id ([TyVar], CType),
  -- Base names of the package's top-level definitions, so lifted-dict
  -- names never collide with a user definition (a user def named
  -- _lifted_dictN is legal)
  topLevelBases :: S.Set FString,
  -- Name of the package being compiled (for qualified lifted ids)
  packageName :: Id,
  symt :: SymTab
}

type L t a = State (LState t) a

initLState :: ErrorHandle -> Flags -> SymTab -> CPackage -> LState a
initLState errh fs r (CPackage mi exps imps impsigs fixs ds includes) = LState {
  errHandle = errh,
  flags = fs,
  dictNo = 0,
  dictPool = M.empty,
  liftedDefs = [],
  liftedTypes = M.empty,
  convEnv = instConvEnv,
  localInstInfo = instInfo,
  topLevelBases = S.fromList [ getIdBase (getDName def) | CValueSign def <- ds ],
  packageName = mi,
  symt = r
}
  where instInfo = M.fromList [ (i, (vs, t))
                              | CValueSign (CDefT i vs (CQType [] t) _) <- ds,
                                isDictFun t ]
        -- Reference nodes for the package's converted-instance
        -- definitions, at exactly the type iConvPackage will later
        -- give their real definitions (the iConvVS formula).  The
        -- entries are lazy; only the ones a lifted dictionary actually
        -- references are ever forced.
        instConvEnv = M.mapWithKey mkRef instInfo
        mkRef i (vs, t) =
            let it = foldr (\ (TyVar v _ k) acc -> ITForAll v (iConvK k) acc)
                           (iConvT fs r t) vs
            in  ICon i (ICDef it (icUndetAt (getIdPosition i) it UNoMatch))

getTopNameInfo :: Id -> L a (Maybe ([TyVar], CType))
getTopNameInfo i = do
    ltmap <- gets liftedTypes
    localMap <- gets localInstInfo
    r <- gets symt
    return $ lookupLifted ltmap <|> lookupLocal localMap <|> lookupSymTab r
  where lookupLifted = fmap (\t -> ([], t)) . M.lookup i
        lookupLocal  = M.lookup i
        lookupSymTab = fmap handleVarInfo . flip findVar i
        handleVarInfo vi@(VarInfo {}) = (tyVars, t')
          where (_ :>: Forall ks qt) = vi_assump vi
                tyVars = zipWith tVarKind tmpTyVarIds ks
                t'     = inst (map TVar tyVars) (qualToType qt)

newDictId :: Position -> L a Id
newDictId pos = do
  n <- gets dictNo
  mi <- gets packageName
  taken <- gets topLevelBases
  -- skip any name a user definition already claims
  let fresh k | getIdBase (enumId "lifted_dict" pos k) `S.member` taken = fresh (k + 1)
              | otherwise = k
      n' = fresh n
  modify (\s -> s { dictNo = n' + 1 })
  return $ qualId mi $ addIdProps (enumId "lifted_dict" pos n') [IdPDict, IdPCAF]

isIncoherentDict :: Id -> Bool
isIncoherentDict i = isDictId i && hasIdProp i IdPIncoherent

type BoundDicts = S.Set Id

-- Convert a liftable dictionary's type and evidence to ISyntax, using
-- the production conversion machinery over the pass's environment (see
-- convEnv above).
convDict :: CType -> CExpr -> L a (IType, IExpr a)
convDict t e = do
  s <- get
  let it = iConvT (flags s) (symt s) t
      ie = iConvExpr (errHandle s) (flags s) (symt s) (convEnv s) e
  return (it, ie)

-- Handle a candidate dictionary definition: simplify its evidence, and
-- if it is liftable, convert it and either reuse a structurally equal
-- previously lifted dictionary of the same interned type or add a new
-- lifted definition.  Right i means the definition can be replaced by
-- a reference to i; Left e' keeps the (possibly simplified) local
-- definition.
handleDict :: Bool -> BoundDicts -> CType -> CExpr -> L a (Either CExpr Id)
handleDict incoherent p t e = do
  (e', liftable) <- handleDictExpr p t e
  if not liftable then do
    when trace_lift_dicts $ traceM $ "Not lifting: " ++ ppReadable t
    return $ Left e'
  else case e' of
    CVar i' -> return $ Right i'
    CApply (CVar i') [] -> return $ Right i'
    _ -> do
      (it, ie) <- convDict t e'
      pool <- gets dictPool
      let cands = M.findWithDefault [] it pool
      case [ i0 | (i0, ie0) <- cands, ie0 == ie ] of
        (i0:_) -> do
          when trace_lift_dicts $ traceM $ "dictPool hit: " ++ ppReadable (i0, t)
          return $ Right i0
        [] -> do
          when (trace_lift_dicts && not (null cands)) $ traceM $
              "dictPool type collision (different evidence): " ++ ppReadable t
          lift_i0 <- newDictId (getPosition e)
          let lift_i = if incoherent then addIdProp lift_i0 IdPIncoherent
                       else lift_i0
          when trace_lift_dicts $ traceM $
              "adding lifted dict: " ++ ppReadable (lift_i, e')
          let ref = ICon lift_i (ICDef it (icUndetAt (getIdPosition lift_i) it UNoMatch))
          modify (\s -> s {
              dictPool = M.insertWith (\new old -> old ++ new) it [(lift_i, ie)] (dictPool s),
              liftedDefs = IDef lift_i it ie [] : liftedDefs s,
              liftedTypes = M.insert lift_i t (liftedTypes s),
              convEnv = M.insert lift_i ref (convEnv s) })
          return $ Right lift_i

handleDictExpr :: BoundDicts -> CType -> CExpr -> L a (CExpr, Bool)
handleDictExpr _ t e
  | (f, [arg]) <- splitTAp t,
    leftCon f == (Just $ idMonad noPosition),
    leftCon arg == Just idActionValue = do
      when trace_lift_dicts $ traceM $ "Not lifting Monad ActionValue: " ++ ppReadable (t, e)
      return (e, False)
handleDictExpr _ _ e
  | tvFree = return (e, False)
  where tvFree = not $ null $ tv e
-- Invariant (typechecker): dictionary evidence is never an undefined
-- value; TCheck constructs dictionaries only from instances, givens,
-- superclass selection, and letrec-bound recursion.
handleDictExpr p t e@(CAnyT {}) = internalError $ "LiftDicts: undefined dictionary value (typechecker invariant violated): " ++ ppReadable (p, t, e)
-- A dictionary given as a struct literal is liftable only when its
-- fields are closed: every free variable must be known at the top
-- level (the free-tyvar guard above has already run).  A field
-- capturing a local would otherwise be lifted into a top-level def
-- with an unbound reference.
handleDictExpr p _ e@(CStructT _ _) = do
  let fvs = fvSetToFreeVars (getFVE e)
  known <- mapM getTopNameInfo fvs
  let closed = not (any (`S.member` p) fvs) &&
               and [ maybe False (const True) k | k <- known ]
  return (e, closed)
handleDictExpr p t e@(CApply f []) = do
  when trace_lift_dicts $ traceM $ "Normalizing CApply f []: " ++ ppReadable e
  handleDictExpr p t f
handleDictExpr p _ e@(CVar i)
  | i `S.member` p = do
      when trace_lift_dicts $ traceM $ "inlining: " ++ ppReadable (i, e)
      return (e, False)
  | otherwise = do
      minfo <- getTopNameInfo i
      case minfo of
        -- Invariant (typechecker + processCDeflsSeq/Cletrec above): every
        -- dictionary variable is lambda/pattern-bound (in BoundDicts),
        -- letrec-bound (in BoundDicts), or a known top-level name.
        Nothing -> internalError $ "LiftDicts: dict variable neither bound nor top-level (scoping invariant violated): " ++ ppReadable i
        Just (vs, t)
          | null vs -> return $ (e, True)
          | otherwise -> internalError $ "handleDictExpr found polymorphic variable where concrete dictionary was expected: " ++ ppReadable (i, vs, t)
handleDictExpr p t e@(CApply f args) = do
  fTy <- handleDictFun [] f
  -- Don't check the result type against dictType because we trust the typechecker
  let argTys = fst $ getArrows fTy
  -- zipWithM would silently drop arguments if the function type showed
  -- fewer arrows than there are arguments (e.g. an arrow hidden behind
  -- an unexpanded synonym)
  when (length argTys < length args) $ internalError $
      "LiftDicts.handleDictExpr: fewer arrows than arguments: " ++
      ppReadable (t, e, fTy)
  (args', liftables) <- fmap unzip $ zipWithM (handleDictExpr p) argTys args
  let e' = CApply f args'
  return (e', and liftables)
handleDictExpr p t e@(CTApply f []) = do
  when trace_lift_dicts $ traceM $ "Normalizing CTApply f []: " ++ ppReadable e
  handleDictExpr p t f
handleDictExpr p t e@(CTApply f ts)
  | not $ null $ tv ts = return (e, False)
  | otherwise          = do
      fTy <- handleDictFun [] e
      when (expandSyn t /= expandSyn fTy) $ internalError $ "Dictionary type does not match expectation: " ++ ppReadable (fTy, t, e)
      return (e, True)
handleDictExpr p t e = internalError $ "handleDictExpr unexpected expression: " ++ ppReadable (p, t, e) ++ "\n" ++ show e

-- Returns the type of the dictionary function
-- should be: dictArg1 -> dictArg2 -> ... -> finalDict
-- instantiates types if the dictionary function is polymorphic
handleDictFun :: [CType] -> CExpr -> L a CType
handleDictFun ts (CVar i) = do
  minfo <- getTopNameInfo i
  case minfo of
    Nothing -> internalError $ "handleDictFun could not find info on an identifier: " ++ ppReadable i
    Just (vs, t) -> if length vs == length ts
                    then return $ apSub (mkSubst (zip vs ts)) t
                    else internalError $ "handleDictFun free variables did not match the number of type arguments available: " ++ ppReadable (i, t, vs, ts)
handleDictFun ts e@(CSelectT ti i) = do
  r <- gets symt
  case findField r i of
    Just xs -> do
      let fis = [ fi | fi <- xs, qualEq ti (fi_id fi) ]
      case [ sc | (_ :>: sc) <- map fi_assump fis ] of
        [sc@(Forall ks qualTy)] -> do
          when (length ts /= length ks) $
            internalError $ "Available type arguments do not match number expected by field selector: " ++
                            ppReadable (e, sc, ts)
          return $ qualToType $ inst ts qualTy
        scs -> internalError $ "handleDictFun CSelectT could not find unique FieldInfo: " ++ ppReadable (ti, i, fis)
    Nothing -> internalError$ "handleDictFun CSelectT field info not found: " ++ ppReadable (ti, i)
handleDictFun ts e@(CAnyT _ _ t) = internalError $ "handleDictFun undefined (CAnyT): " ++ ppReadable (ts, t, e)
handleDictFun ts0 (CTApply f ts)
  | null ts0 = handleDictFun ts f
  | otherwise = internalError $ "handleDictFunc stacked CTApply: " ++ ppReadable (ts0, f, ts)
handleDictFun ts (Cletseq [CLValueSign (CDefT id_f [] (CQType [] ty) _) []] (CVar id_f'))
  | id_f == id_f' = return ty
handleDictFun ts e = internalError $ "handleDictFun unexpected expression: " ++ ppReadable (ts, e) ++ "\n" ++ show e

-- General inlining map (more than dictionaries):
-- - Constants
-- - undefined expressions
-- - variable to variable assignments
type InlineMap = M.Map Id CExpr

-- InlineMap is used for substitution but not returned (scoped bindings don't escape).
-- Only special functions (processCDeflsSeq, processCQuals) return InlineMap for sequential threading.
class LiftDicts c where
  liftDicts :: BoundDicts -> InlineMap -> c -> L a c

-- General instance when there is no sequential scoping
instance LiftDicts c => LiftDicts [c] where
  liftDicts p m = mapM (liftDicts p m)

instance LiftDicts CDefn where
  liftDicts p m (CValueSign def) = do
    CValueSign <$> liftDicts p m def
  -- Do nothing to other top-level definitions (Cdata, Cstruct, Ctype, ...)
  liftDicts _ _ d = return d

instance LiftDicts CDef where
  liftDicts p m (CDefT i vs cqt cs) =
    CDefT i vs cqt <$> liftDicts p m cs
  liftDicts _ _ def = internalError $ "LiftDicts - unexpected CDef: " ++ ppReadable def

shadowBindings :: S.Set Id -> InlineMap -> InlineMap
shadowBindings s m = M.withoutKeys m s

instance LiftDicts CClause where
  liftDicts p m (CClause ps qs e) = do
    let p' = p `S.union` S.fromList [ i | CPVar i <- ps, isDictId i ]
        pvs = S.unions $ map getPV ps
        m' = shadowBindings pvs m
    (qs', m'') <- processCQuals p' m' qs
    e' <- liftDicts p' m'' e
    return $ CClause ps qs' e'

-- We handle CQuals separately because we need to update the inlineMap as entries are shadowed
processCQuals :: BoundDicts -> InlineMap -> [CQual] -> L a ([CQual], InlineMap)
processCQuals _ m [] = return ([], m)
processCQuals p m (CQGen t pat e : qs) = do
  -- CQGen binds e to the pattern, so does not shadow anything in e
  e' <- liftDicts p m e
  let pvs = getPV pat
      m' = shadowBindings pvs m
  (qs', m'') <- processCQuals p m' qs
  return $ (CQGen t pat e' : qs', m'')
processCQuals p m (CQFilter e : qs) = do
  e' <- liftDicts p m e
  (qs', m') <- processCQuals p m qs
  return (CQFilter e' : qs', m')

instance LiftDicts CDefl where
  liftDicts p m (CLValueSign d qs) = do
    (qs', m') <- processCQuals p m qs
    d' <- liftDicts p m' d
    return $ CLValueSign d' qs'
  liftDicts _ _ defl =
    internalError $ "LiftDicts unexpected CDefl: " ++ ppReadable defl

isSimple :: CExpr -> Bool
isSimple (CAnyT _ _ _) = True
isSimple (CLitT _ _) = True
isSimple (CConT _ _ []) = True
isSimple (CStructT _ []) = True
isSimple (CApply f []) = isSimple f
isSimple (CTApply f []) = isSimple f
-- CVar is not simple because we have to do capture analysis for non-dictionaries
-- CTApply is not simple because type applications are work
isSimple _ = False

simpCExpr :: CExpr -> CExpr
simpCExpr (CApply f []) = simpCExpr f
simpCExpr (CTApply e []) = simpCExpr e
simpCExpr e = e


data DeflAction = Inline Id CExpr | Keep CDefl

deflAction :: BoundDicts -> CDefl -> L a DeflAction
deflAction p (CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) [])
  | isSimple e && not (isKeepId i) = do
      when trace_lift_dicts $ traceM  $ "inlining simple: " ++ ppReadable (i, e)
      return $ Inline i $ simpCExpr e
  -- keep-id simple definitions fall through: a keep-id dictionary
  -- still participates in the dictionary handling below
  -- Dictionary variables are safe to inline because the typechecker
  -- mints them fresh per top-level definition (_tcdictN): shadowBindings
  -- removes re-bound KEYS from the InlineMap, and this freshness is what
  -- guarantees no surviving entry's VALUE mentions a re-bound id.
  | isDictId i, CVar _ <- e = do
      when trace_lift_dicts $ traceM  $ "inlining dict var: " ++ ppReadable (i, e)
      return $ Inline i e
  | isDictId i = do
      result <- handleDict (isIncoherentDict i) p t e
      case result of
        -- Dictionary was lifted, safe to inline
        Right i' -> do
          when trace_lift_dicts $ traceM $ "inlining lifted dict: " ++ ppReadable (i, i')
          return $ Inline i (CVar i')
        -- Dictionary expression may have been simplified, but it could not be lifted.
        -- Therefore we keep the definition with the updated expression.
        Left e' -> do
          when trace_lift_dicts $ traceM $ "dictionary expression not lifted: " ++ ppReadable (i, e)
          return $ Keep $ CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e']) []
deflAction _ d = return $ Keep d

processCDeflsSeq :: BoundDicts -> InlineMap -> [CDefl] -> L a ([CDefl], InlineMap)
processCDeflsSeq _ m [] = return ([], m)
processCDeflsSeq p m (d:ds) = do
  d' <- liftDicts p m d
  action <- deflAction p d'
  case action of
    Inline i e -> do
      let m' = M.insert i e m
      processCDeflsSeq p m' ds
    Keep d'' -> do
      let i = getLName d''
      let m' = shadowBindings (S.singleton i) m
      let p' = if isDictId i then S.insert i p else p
      (ds', m'') <- processCDeflsSeq p' m' ds
      return (d'':ds', m'')

instance LiftDicts CExpr where
  liftDicts p m (Cletseq ds e) = do
    (ds', m') <- processCDeflsSeq p m ds
    e' <- liftDicts p m' e
    return $ cLetSeq ds' e'
  -- We are not attempting to lift recursive dictionary bindings for now;
  -- the letrec-bound dictionary ids join BoundDicts so that a nested
  -- dictionary expression referencing one is (correctly) not lifted,
  -- rather than tripping the top-level-known internalError below.
  liftDicts p m (Cletrec ds e) = do
    let vs = S.fromList [ getLName d | d <- ds ]
        m' = shadowBindings vs m
        p' = p `S.union` S.filter isDictId vs
    ds' <- liftDicts p' m' ds
    e'  <- liftDicts p' m' e
    return $ cLetRec ds' e'
  liftDicts p m (CApply f es) = do
    f'  <- liftDicts p m f
    es' <- liftDicts p m es
    return $ CApply f' es'
  liftDicts p m (CTApply e ts) = do
    e' <- liftDicts p m e
    return $ CTApply e' ts
  liftDicts p m e@(CVar i) = do
    case M.lookup i m of
      -- The inlined expression keeps its definition-site position: use
      -- sites of CSEd/lifted dictionaries and inlined constants report
      -- (and name nets after) where the value was defined, not where it
      -- was used.  This is a deliberate tradeoff; re-positioning the
      -- expression per use site would defeat the sharing.
      Just e' -> return e'
      Nothing -> return e
  liftDicts p m (CTaskApplyT task t es) = do
    es' <- liftDicts p m es
    return $ CTaskApplyT task t es'
  liftDicts p m (Crules sps rs) = do
    rs' <- liftDicts p m rs
    return $ Crules sps rs'
  liftDicts p m (CConT ti con es) = do
    es' <- liftDicts p m es
    return $ CConT ti con es'
  liftDicts p m (CStructT ct fields) = do
    fields' <- mapSndM (liftDicts p m) fields
    return $ CStructT ct fields'
  liftDicts p m (CmoduleVerilogT ty name ui clks rst args fields sch paths) = do
    name' <- liftDicts p m name
    args' <- mapSndM (liftDicts p m) args
    return $ CmoduleVerilogT ty name' ui clks rst args' fields sch paths
  liftDicts _ _ e = return e

instance LiftDicts CRule where
  liftDicts p m (CRule rps name qs e) = do
    name' <- mapM (liftDicts p m) name
    (qs', m') <- processCQuals p m qs
    e' <- liftDicts p m' e
    return $ CRule rps name' qs' e'
  liftDicts p m (CRuleNest rps name qs rs) = do
    name' <- mapM (liftDicts p m) name
    (qs', m') <- processCQuals p m qs
    rs' <- liftDicts p m' rs
    return $ CRuleNest rps name' qs' rs'
