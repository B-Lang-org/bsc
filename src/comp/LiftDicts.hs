module LiftDicts(liftDictsPkg) where

import Control.Applicative((<|>))
import Control.Monad(when, zipWithM)
import Control.Monad.State.Strict
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Debug.Trace({- trace, -} traceM)

import ErrorUtil(internalError)
import IOUtil(progArgs)
import Util(mapSndM, tracep)

import CSyntax
import CFreeVars(getPV)
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

trace_lift_dicts :: Bool
trace_lift_dicts = "-trace-lift-dicts" `elem` progArgs

liftDictsPkg :: SymTab -> CPackage -> CPackage
liftDictsPkg symt pkg@(CPackage mi exps imps fixs ds includes) = CPackage mi exps imps fixs ds'' includes
  where s = initLState symt pkg
        (ds', s') = runState (liftDicts S.empty M.empty ds) s
        lifted_ds = [ CValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) |
                      (i, (t, e)) <- M.toList $ liftedDictMap s' ]
        ds'' = ds' ++ lifted_ds

data LState = LState {
  -- source of unique numbers to append to top-level dict names
  dictNo :: !Int,
  -- Coherent dictionaries: Map of types to top-level name
  -- Coherent dictionaries of the same type are semantically equivalent
  -- and we take advantage of this during our lifting.
  typeDictMap :: !(M.Map CType Id),
  -- Incoherent dictionaries: Map of CSEd expressions to top-level
  -- dict references. Incoherent dictionary matches cannot be safely
  -- mapped to a single type, but we still want as much CSE and reuse
  -- as we can get.
  exprDictMap :: !(M.Map CExpr Id),
  -- Dictionaries lifted during this pass. Maps dictionary Id to its type
  -- and expression. Lifted dictionaries are always monomorphic (no type
  -- variables) and have no dictionary parameters. Any dictionary parameters
  -- that were there on the instance have been resolved to references to
  -- top-level dictionary functions and required arguments. A CDefn for
  -- the lifted dictionary can be reconstructed from this information
  -- at the end of the pass.
  liftedDictMap :: !(M.Map Id (CType, CExpr)),
  -- Information about instances that do not appear in the symbol table.
  -- These are converted instance definitions that were added by convinst
  -- but never incorporated into the symbol table.
  localInstInfo :: !(M.Map Id ([TyVar], CType)),
  -- Name of the package being compiled (for qualified lifted ids)
  packageName :: !Id,
  symt :: !SymTab
}

type L a = State LState a

initLState :: SymTab -> CPackage -> LState
initLState symt (CPackage mi exps imps fixs ds includes) = LState {
  dictNo = 0,
  typeDictMap = M.empty,
  exprDictMap = M.empty,
  liftedDictMap = M.empty,
  localInstInfo = M.fromList [ (i, (vs, t)) | CValueSign (CDefT i vs (CQType [] t) _) <- ds, isDictFun t ],
  packageName = mi,
  symt = symt
}

getTopNameInfo :: Id -> L (Maybe ([TyVar], CType))
getTopNameInfo i = do
    ldmap <- gets liftedDictMap
    localMap <- gets localInstInfo
    r <- gets symt
    return $ lookupLifted ldmap <|> lookupLocal localMap <|> lookupSymTab r
  where lookupLifted = fmap (\(t,_) -> ([], t)) . M.lookup i
        lookupLocal  = M.lookup i
        lookupSymTab = fmap handleVarInfo . flip findVar i
        handleVarInfo (VarInfo _ (_ :>: Forall ks qt) _) = (tyVars, t')
          where tyVars = zipWith tVarKind tmpTyVarIds ks
                t'     = inst (map TVar tyVars) (qualToType qt)

newDictId :: Position -> L Id
newDictId pos = do
  n <- gets dictNo
  mi <- gets packageName
  modify (\s -> s { dictNo = n + 1 })
  return $ qualId mi $ addIdProps (enumId "lifted_dict" pos n) [IdPDict, IdPCAF]

type BoundDicts = S.Set Id

handleCoherentDict :: BoundDicts -> CType -> CExpr -> L (Either CExpr Id)
handleCoherentDict p t e = do
  tdm <- gets typeDictMap
  case M.lookup t tdm of
    Just i -> do
      when trace_lift_dicts $ traceM $ "typeDictMap hit: " ++ ppReadable (i, t)
      return $ Right i
    Nothing -> do
      when trace_lift_dicts $ traceM $ "typeDictMap miss: " ++ ppReadable t
      (e', liftable) <- handleDictExpr p t e
      if not liftable then return $ Left e'
      else do
        i <- newDictId (getPosition e)
        when trace_lift_dicts $ traceM $ "adding lifted dict (coherent): " ++ ppReadable (i, e')
        modify (\s -> s { liftedDictMap = M.insert i (t, e') $ liftedDictMap s,
                          typeDictMap = M.insert t i $ typeDictMap s })
        return $ Right i

handleIncoherentDict :: BoundDicts -> CType -> CExpr -> L (Either CExpr Id)
handleIncoherentDict p t e = do
  (e', liftable) <- handleDictExpr p t e
  if not liftable then return $ Left e'
  else do
    edm <- gets exprDictMap
    case M.lookup e' edm of
      Just i -> do
        when trace_lift_dicts $ traceM $ "exprDictMap hit: " ++ ppReadable (i, e')
        return $ Right i
      Nothing -> do
        when trace_lift_dicts $ traceM $ "exprDictMap miss: " ++ ppReadable e'
        i <- newDictId (getPosition e)
        let i' = addIdProp i IdPIncoherent
        when trace_lift_dicts $ traceM $ "adding lifted dict (incoherent): " ++ ppReadable (i', e')
        modify (\s -> s { liftedDictMap = M.insert i' (t, e') $ liftedDictMap s,
                          exprDictMap = M.insert e' i' $ exprDictMap s })
        return $ Right i'

handleDictExpr :: BoundDicts -> CType -> CExpr -> L (CExpr, Bool)
handleDictExpr _ t e
  | (f, [arg]) <- {- trace ("trying to lift type: " ++ ppReadable t) -} splitTAp t,
    leftCon f == (Just $ idMonad noPosition),
    leftCon arg == Just idActionValue = do
      when trace_lift_dicts $ traceM $ "Not lifting Monad ActionValue: " ++ ppReadable (t, e)
      return (e, False)
handleDictExpr _ _ e
  | tvFree = return (e, False)
  where tvFree = not $ null $ tv e
handleDictExpr _ _ e@(CAnyT {}) = return (e, True)
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
        Nothing -> internalError $ "handleDictExpr dict variable not bound param or known at the top level: " ++ ppReadable i
        Just (vs, t)
          | null vs -> return $ (e, True)
          | otherwise -> internalError $ "handleDictExpr found polymorphic variable where concrete dictionary was expected: " ++ ppReadable (i, vs, t)
handleDictExpr p t e@(CApply f args) = do
  fTy <- handleDictFun [] f
  -- Don't check the result type against dictType because we trust the typechecker
  let argTys = fst $ getArrows fTy
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
handleDictFun :: [CType] -> CExpr -> L CType
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
handleDictFun [] (CAnyT _ _ t) = return t
handleDictFun ts (CAnyT _ _ _) = internalError $ "handleDictFun polymorphic CAnyT: " ++ ppReadable ts
handleDictFun ts0 (CTApply f ts)
  | null ts0 = handleDictFun ts f
  | otherwise = internalError $ "handleDictFunc stacked CTApply: " ++ ppReadable (ts0, f, ts)
handleDictFun ts e = internalError $ "handleDictFun unexpected expression: " ++ ppReadable (ts, e) ++ "\n" ++ show e

-- General inlining map (more than dictionaries):
-- - Constants
-- - undefined expressions
-- - variable to variable assignments
type InlineMap = M.Map Id CExpr

-- InlineMap is used for substitution but not returned (scoped bindings don't escape).
-- Only special functions (processCDeflsSeq, processCQuals) return InlineMap for sequential threading.
class LiftDicts a where
  liftDicts :: BoundDicts -> InlineMap -> a -> L a

-- General instance when there is no sequential scoping
instance LiftDicts a => LiftDicts [a] where
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
processCQuals :: BoundDicts -> InlineMap -> [CQual] -> L ([CQual], InlineMap)
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

{-
setPositionSimp :: Position -> CExpr -> CExpr
setPositionSimp pos (CVar i) = CVar $ setIdPosition pos i
setPositionSimp pos (CLitT t (CLiteral _ l)) = CLitT t (CLiteral pos l)
setPositionSimp pos (CAnyT _ uk t) = CAnyT pos uk t
setPositionSimp pos (CConT t c es) = CConT t (setIdPosition pos c) es
setPositionSimp _ e = e -- not handling CStructT yet
-}

data DeflAction = Inline Id CExpr | Keep CDefl

deflAction :: BoundDicts -> CDefl -> L DeflAction
deflAction p (CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) [])
  | isSimple e && not (isKeepId i) = do
      when trace_lift_dicts $ traceM  $ "inlining simple: " ++ ppReadable (i, e)
      return $ Inline i $ simpCExpr e
  | isSimple e && (tracep trace_lift_dicts ("simple not inlined: " ++ ppReadable (i, e)) False) = internalError "unpossible"
  -- Dictionary variables are safe to inline because they are unique per top-level definition
  | isDictId i, CVar _ <- e = do
      when trace_lift_dicts $ traceM  $ "inlining dict var: " ++ ppReadable (i, e)
      return $ Inline i e
  | isDictId i = do
      let handler = if isIncoherentDict i then handleIncoherentDict else handleCoherentDict
      result <- handler p t e
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

processCDeflsSeq :: BoundDicts -> InlineMap -> [CDefl] -> L ([CDefl], InlineMap)
processCDeflsSeq _ m [] = return ([], m)
processCDeflsSeq p m (d:ds) = do
  d' <- liftDicts p m d
  action <- deflAction p d'
  case action of
    Inline i e -> do
      let m' = M.insert i e m
      processCDeflsSeq p m' ds
    Keep d'' -> do
      let m' = shadowBindings (S.singleton $ getLName d'') m
      (ds', m'') <- processCDeflsSeq p m' ds
      return (d'':ds', m'')

instance LiftDicts CExpr where
  liftDicts p m (Cletseq ds e) = do
    (ds', m') <- processCDeflsSeq p m ds
    e' <- liftDicts p m' e
    return $ cLetSeq ds' e'
  -- We are not attempting to lift recursive dictionary bindings for now
  liftDicts p m (Cletrec ds e) = do
    let vs = S.fromList [ getLName d | d <- ds ]
        m' = shadowBindings vs m
    ds' <- liftDicts p m' ds
    e'  <- liftDicts p m' e
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
      Just e' -> return $ e' -- setPositionSimp (getPosition i) e'
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

