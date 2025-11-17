{-# LANGUAGE CPP #-}
module TIMonad(
        TI,
        apSubTI, Bind, mkDefl,
        runTI, err, errs, twarn, handle,
        getAllowIncoherent, maskAllowIncoherent,
        getFlags, setFlags, getSymTab,
        getSubst, clearSubst, extSubst, updSubst,
        newTVar, newTVarId, isNewTVar, newDict, newVar,
        freshInst,
        VPred(..), getVPredPositions, nubVPred, expandSynVPred,
        EPred(..), Infer2, CheckT, TaskCheckT,
        getBoundTVs, getTopBoundTVs, addBoundTVs, popBoundTVs,
        getExplPreds, getTopExplPreds, addExplPreds, popExplPreds, mkEPred,
        errorAtId, findCons, findTyCon, findFields, findCls,
        bitCls,
        literalCls, realLiteralCls, sizedLiteralCls, stringLiteralCls,
        numEqCls,
        updAssumpPos,
        recordPackageUse,
        incrementSatStack, decrementSatStack, getSatStack, mkTSSatElement, TSSatElement,
              pushSatStackContext, popSatStackContext
        , tiRecoveringFromError
        , tiRecoveringFromErrorxx
        , disambiguateStruct
        ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import PFPrint
import Id
import IdPrint
import Position
import CSyntax(CExpr(..), CDef(..), CDefl(..), CClause(..))
import CType
import Error(internalError, EMsg, WMsg, EMsgs(..), ErrMsg(..))
import Flags(Flags, maxTIStackDepth)
import Subst
import Pred
import Scheme
import Assump
import SymTab
import PreIds(idBits, idLiteral, idRealLiteral, idSizedLiteral,
              idStringLiteral, idNumEq)
import Control.Monad(when)
import Control.Monad.Except(ExceptT, runExceptT, throwError, catchError)
import Control.Monad.State(State, StateT, runState, runStateT,
                           lift, gets, get, put, modify)
import Data.List(partition)
import qualified Data.Set as S
import Util(headOrErr)

-------

import Debug.Trace(traceM)
import IOUtil(progArgs)

doVarTrace, doSubstTrace, dontTrim :: Bool
doVarTrace = elem "-trace-tcvar" progArgs
doSubstTrace = elem "-trace-type-extsubst" progArgs
dontTrim = elem "-trace-skip-trim" progArgs

-------

-- typechecking state that persists across errors
data TStatePersistent = TStatePersistent {
   tsFlags :: Flags,
   tsSymTab :: SymTab, -- symbol table
   tsNextTyVar :: !Int, -- index of the next generated tyvar
   tsRecoveredErrors :: [EMsg],
     -- accumulated error messages from which we have recovered
   -- whether TI monad allows general incoherent instance matches
   -- or only for marked typeclasses
   tsAllowIncoherent :: Bool,
   tsWarns :: [WMsg], -- accumulated warning messages
   tsUsedPackages :: S.Set Id -- packages from which symbols were used
}

-- typechecking state that is restored in case of error
data TStateRecover = TStateRecover {
  tsCurSubst :: !Subst, -- current substitution
  -- stack of bound tyvars (list of lists for stuff bound at each level)
  tsBoundTyVarStack :: [[TyVar]],
  tsExplPreds :: [[EPred]],
  tsSatStack :: TSSuperSatStack
}

type TSSatElement = EPred

mkTSSatElement :: (Maybe [TyVar]) -> [EPred] -> VPred -> TSSatElement
-- this solves a VPred in a circular way by simply assigning the
-- variable to the pred.  We still will need to solve the pred "p".
-- It is useful when there is recursion, where the solved "p" will
-- refer right back to this predicate.
mkTSSatElement _ _ (VPred i (PredWithPositions p _)) = EPred (CVar i) p

type TSSatStack = SizedStack TSSatElement
type TSSuperSatStack = SizedStack TSSatStack

-- a stack that keeps track of its depth
data SizedStack a = SizedStack Int [a]

mkSizedStack :: [a] -> SizedStack a
mkSizedStack v = SizedStack (length v) v

sizedStackPush
  :: ( Monad m
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 808)
     , MonadFail m
#endif
     ) => Int -> SizedStack a -> a -> m (SizedStack a)
sizedStackPush maxStackDepth (SizedStack size stack) x =
    if ( size >= maxStackDepth )
        then fail "stack overflow"
        else return (SizedStack (succ size) (x:stack))

sizedStackPop :: SizedStack a -> SizedStack a
sizedStackPop (SizedStack size (_:rest)) =
    SizedStack (pred size) rest
sizedStackPop _ = internalError "sizedStackPop: stack underflow"

sizedStackPeek :: SizedStack a -> a
sizedStackPeek (SizedStack size (x:_)) = x
sizedStackPeek _ = internalError "sizedStackPeek: stack underflow"

sizedStackModify :: SizedStack a -> (a -> a) -> SizedStack a
sizedStackModify (SizedStack size (x:rest)) f =
    SizedStack size ((f x):rest)
sizedStackModify _ _ = internalError "sizedStackModify: stack underflow"

-- state/error monad with bsc error messages and hidden TState
type TI = StateT TStateRecover (ExceptT EMsgs (State TStatePersistent))

-- apply the current substitution to something
apSubTI :: (Types a) => a -> TI a
apSubTI x = do
              subst <- getSubst
              return (apSub subst x)

initPersistentState :: Flags -> Bool -> SymTab -> TStatePersistent
initPersistentState flags ai s = TStatePersistent {
    tsFlags = flags,
    tsSymTab = s,
    tsNextTyVar = 1000,
    tsWarns = [],
    tsAllowIncoherent = ai,
    tsRecoveredErrors = [],
    tsUsedPackages = S.empty
  }

initRecoverState :: TStateRecover
initRecoverState = TStateRecover {
    tsCurSubst = nullSubst,
    tsBoundTyVarStack = [],
    tsExplPreds = [],
    tsSatStack = mkSizedStack [mkSizedStack []]
  }

runTI :: Flags -> Bool -> SymTab -> TI a -> (Either [EMsg] a, [WMsg], S.Set Id)
runTI flags ai s m = (final_result, tsWarns pState, tsUsedPackages pState)
  where (result, pState) = runState error_run
                                    (initPersistentState flags ai s)
        error_run = (runExceptT (runStateT m initRecoverState))
        rec_errors = tsRecoveredErrors pState
        final_result =
            case result of
              Left es -> Left ((errmsgs es) ++ rec_errors)
              Right (answer, _) ->
                  case rec_errors of
                    [] -> Right answer
                    es -> Left es

-- Add an error from which we have recovered to the accumulating list of
-- such errors.  If you forget to call this function in your error handler
-- (i.e., second argument to catchError), the error will be ignored and
-- the TI Monad will succeed.
accumulateError :: EMsgs -> TI ()
accumulateError es = do
  -- traceM "hello accumulateError"
  lift (modify addError)
  -- list might have poor time complexity when building
  -- this kind of concatenation. XXX
  -- Possibly explore "finger trees" in the future.
  where addError s = s { tsRecoveredErrors = (tsRecoveredErrors s) ++ (errmsgs es) }

-- XXX maybe someday get rid of the next two functions and replace them with
-- throwError.  But throwError requires importing Control.Monad.Error
err :: EMsg -> TI a
err e = throwError (EMsgs [e])

errs :: String -> [EMsg] -> TI a
errs tag [] = internalError ("TIMonad errs: no errors - " ++ tag)
errs tag es = throwError (EMsgs es)

tiRecoveringFromError :: Types a => TI a -> TI a -> TI a
tiRecoveringFromError = tiRecoveringFromError'
                        -- tiRecoveringFromErrorxx

tiRecoveringFromError' :: Types a => TI a -> TI a -> TI a
tiRecoveringFromError' do_something create_fake_output = do
  oldState {- :: TStateRecover -} <- get
  catchError
     (if dontTrim then do_something else
          (do
       -- the SUCCESS path

       -- getPosition noPosition == noPosition
       -- via "instance HasPosition Position"
            (dummy, _) <- newTVarId "tiRecoveringFromError" KStar noPosition
            answer <- do_something

           {-
             The reason we trimSubst on success is twofold:
             1. As a sanity check to make sure that no type information
             is leaking out of the "do_something" code, and that this
             error recovery framework is sound.
             2. Performance (memory) improvement.
             The reason we getSubst and apSub is if a certain type
             variable is generated in do_something, we do not want
             to trim it away, but force (apSub) it into the returned value.
             (after consultation with Ravi.)
            -}
            s <- getSubst
            updSubst (trimSubst dummy)
            return (apSub s answer)
          ))
     (\es ->
          -- the FAIL path

          do accumulateError es
             put oldState
             -- create_fake_output usually returns some bogus
             -- return value simulating the output of "do_something"
             create_fake_output
     )

-- exists only for debugging
tiRecoveringFromErrorxx :: TI a -> TI a -> TI a
tiRecoveringFromErrorxx do_something _ = do_something

twarn :: WMsg -> TI ()
twarn w = lift (modify (addWarning w))
  where addWarning w s = s { tsWarns = w:(tsWarns s) }

-- Record that a symbol from a package was used
recordPackageUse :: Maybe Id -> TI ()
recordPackageUse Nothing = return ()  -- no package to record
recordPackageUse (Just pkg) = lift (modify (addPackage pkg))
  where addPackage pkg s = s { tsUsedPackages = S.insert pkg (tsUsedPackages s) }

-- XXX maybe someday get rid of this function and replace with catchError
handle :: TI a -> (EMsgs -> TI a) -> TI a
handle = catchError

getAllowIncoherent :: TI Bool
getAllowIncoherent = lift (gets tsAllowIncoherent)

-- temporarily turn off allowIncoherent
-- used for reducePredsAggressive (and possibly other things)
maskAllowIncoherent :: TI a -> TI a
maskAllowIncoherent m = do
  s_p <- lift get
  let old_ai = tsAllowIncoherent s_p
  lift $ put $ s_p  { tsAllowIncoherent = False }
  result <- m
  s_p' <- lift get
  lift $ put $ s_p' { tsAllowIncoherent = old_ai }
  return result

getFlags :: TI Flags
getFlags = lift (gets tsFlags)

setFlags :: Flags -> TI ()
setFlags new_flags = do
  let updFn s = s { tsFlags = new_flags }
  lift (modify updFn)

getSymTab :: TI SymTab
getSymTab = lift (gets tsSymTab)

getSubst :: TI Subst
getSubst = gets tsCurSubst

transSubst :: (Subst -> Subst) -> TStateRecover -> TStateRecover
transSubst f s = s { tsCurSubst = f (tsCurSubst s) }

updSubst :: (Subst -> Subst) -> TI ()
updSubst f = modify (transSubst f)

getBoundTVs :: TI [TyVar]
getBoundTVs = gets tsBoundTyVarStack >>= (return . concat)

-- get just the most recently bound tvars
getTopBoundTVs :: TI [TyVar]
getTopBoundTVs = gets tsBoundTyVarStack >>= (return . headOrErr "getTopBoundTVs")

addBoundTVs :: [TyVar] -> TI ()
addBoundTVs is = modify addVars
  where addVars s = s { tsBoundTyVarStack = is:(tsBoundTyVarStack s) }

popBoundTVs :: TI ()
popBoundTVs = modify dropVars
  where dropVars s = s { tsBoundTyVarStack = tail (tsBoundTyVarStack s) }

getExplPreds :: TI [EPred]
getExplPreds = gets tsExplPreds >>= (return . concat)

getTopExplPreds :: TI [EPred]
getTopExplPreds = gets tsExplPreds >>= (return . headOrErr "getTopExplPreds")

addExplPreds :: [EPred] -> TI ()
addExplPreds ps = modify addPreds
  where addPreds s = s { tsExplPreds = ps : (tsExplPreds s) }

popExplPreds :: TI ()
popExplPreds = modify dropPreds
  where dropPreds s = s { tsExplPreds = tail (tsExplPreds s) }

mkEPred :: Pred -> TI EPred
mkEPred p = do i <- newDict
               return $ EPred (CVar i) p

clearSubst :: TI ()
clearSubst = modify (transSubst (const nullSubst))

extSubst :: String -> Subst -> TI ()
extSubst loc s' = do
  s <- getSubst
  when (doSubstTrace) $ do
    when (not (chkSubstOrder s' s)) $
      internalError(loc ++ " extSubst: " ++ ppReadable (s', s))
    traceM (loc ++ " extSubst: " ++ ppReadable s')
  modify (transSubst (\s -> s' @@ s))

getTyVarNum :: TI (Int)
getTyVarNum = lift $ do
  s <- get
  let n = tsNextTyVar s
  put (s { tsNextTyVar = n + 1 })
  return n

-- XXX consider adding tracing support for string in the name as with newVar
newTVar :: HasPosition a => String -> Kind -> a -> TI Type
newTVar msg k x = do
  let pos = getPosition x
  bvs <- getBoundTVs
  let loopVar = do
        n <- getTyVarNum
        let v = TyVar (enumId "tctyvar" pos n) n k
        if (v `elem` bvs) then loopVar
         else do
           when doVarTrace $ traceM ("newTVar: " ++ show n ++ " " ++ msg);
           return (TVar v)
  loopVar

-- convenience function for getting the TyVar
-- (when create a TVar for marking a place in the subst to trim back to)
newTVarId :: HasPosition a => String -> Kind -> a -> TI (TyVar, Type)
newTVarId msg k x = do
  tv <- newTVar msg k x
  case tv of
    TVar i -> return (i, tv)
    _ -> internalError (msg ++ ": call to newTVarId failed")

-- distinguish TyVars with generated names from those with user-given names
isNewTVar :: TyVar -> Bool
isNewTVar (TyVar i _ _) =
    -- new tvars are created with "enumId" which marks the Id as bad
    isBadId i

newDict :: TI Id
newDict = do
 n <- getTyVarNum
 when doVarTrace $ traceM ("newDict: " ++ ppReadable n)
 return (addIdProp (enumId "tcdict" noPosition n) IdPDict)

newVar :: Position -> String -> TI Id
newVar p str = do
    -- only make the name worse if tracing is on
    let varname = if doVarTrace then "tctemp_"++str++"_" else "tctemp"
    n <- getTyVarNum
    --traceM (ppReadable (p, n)) $
    return (enumId varname p n)

freshInst :: HasPosition a => String -> a -> Scheme -> TI (Qual Type, [Type])
freshInst msg x (Forall ks qt@(_ :=> t)) = do
    ts <- mapM (flip (newTVar ("freshInst " ++ msg)) x) ks
{-
    let ps :=> t = inst ts qt
        ps' = [ IsIn clsSize [t] | t <- ts, kind t == KNum ]
    return ((ps ++ ps') :=> t, ts)
-}
    return (inst ts qt, ts)

------

-- VPred is an unsolved predicate (at least in satisfy, satMany, sat...)
data VPred = VPred Id PredWithPositions
    deriving (Show)

instance Types VPred where
    apSub s (VPred i p) = VPred i (apSub s p)
    tv (VPred _ p) = tv p

instance PPrint VPred where
-- note that the colon (:) that gets printed here is NOT a list cons!
    pPrint d p (VPred i q) = pparen (p>0) (ppId d i <> text":" <> pPrint d 10 q)

getVPredPositions :: VPred -> [Position]
getVPredPositions (VPred i p) = getPredPositions p

-- the best position for a VPred should be its dictionary binding
instance HasPosition VPred where
  getPosition (VPred i p) = getPosition i

-- the CExpr is a dictionary
type Bind = (Id, Type, CExpr)

mkDefl :: Bind -> CDefl
mkDefl (i, t, e) = CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) []

nubVPred :: [VPred] -> CExpr -> ([VPred], CExpr)
nubVPred ps e =
  let (ps', bs) = nubVPred' ps
      defls = map mkDefl bs
  in
      (ps', Cletrec defls e)

nubVPred' :: [VPred] -> ([VPred], [Bind])
nubVPred' [] = ([], [])
nubVPred' (x@(VPred i p):xs) =
    let eq (VPred _ a) (VPred _ b) = (a == b)
        (ps, notps) = partition (eq x) xs
        poss = concatMap getVPredPositions ps
        x' = VPred i (addPredPositions p poss)
        t  = predToType (removePredPositions p)
        bs = [(i', t, CVar i) | (VPred i' _) <- ps]
        (xs', bs') = nubVPred' notps
    in  (x':xs', bs ++ bs')

expandSynVPred :: VPred -> VPred
expandSynVPred (VPred i (PredWithPositions (IsIn c ts) poss)) = VPred i pwp'
  where pwp' = PredWithPositions p' poss
        p'   = IsIn c ts'
        ts'  = map expandSyn ts

-- the CExpr is a dictionary
data EPred = EPred CExpr Pred

instance Types EPred where
    apSub s (EPred e p) = EPred e (apSub s p)
    tv (EPred _ p) = tv p

instance PPrint EPred where
    pPrint d p (EPred e q) = pparen (p>0) (pparen True (pPrint d 0 e) <> text":" <> pPrint d 10 q)

type Infer2 e t r = [Assump] -> e -> TI ([VPred], t, r)

type CheckT e = [Assump] -> Type -> e -> TI ([VPred], e)
type TaskCheckT = [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred], CExpr)

------

errorAtId :: (String -> ErrMsg) -> Id -> TI a
errorAtId econ i =
    let emsg = (getIdPosition i, econ (pfpString i))
    in  err emsg

findCons :: Type -> Id -> TI (Assump, Id)
findCons ct i = do
    -- traceM ("findCons: " ++ show (ct,i))
    r <- getSymTab
    case findConVis r i of
     Just [ConInfo { ci_id = ti, ci_assump = a, ci_pkg = pkg }] -> do
        recordPackageUse pkg
        return (updAssumpPos i a, ti)
     Just cs -> do
        s <- getSubst
        let ct' = apSub s ct
        case leftCon (expandSyn ct') of
         Nothing -> errorAtId (EConstrAmb (pfpString ct')) i
         Just di -> case [ (a, pkg) | ConInfo {ci_id = i', ci_assump = a, ci_pkg = pkg} <- cs, qualEq di i'] of
                   [(a, pkg)] -> do
                       recordPackageUse pkg
                       return (updAssumpPos i a, di)
                   []  -> errSuggest r i
                   _   -> internalError "findCons ambig"
     Nothing -> errSuggest r i
  where
    errSuggest :: SymTab -> Id -> TI (Assump, Id)
    errSuggest r i =
      let mSuggest = case findType r i of
            Just (TypeInfo _ KNum _ _ _) -> Just "valueOf"
            Just (TypeInfo _ KStr _ _ _) -> Just "stringOf"
            _ -> Nothing
      in err (getIdPosition i, EUnboundCon (pfpString i) mSuggest)

findTyCon :: Id -> TI TyCon
findTyCon i = do
    r <- getSymTab
    case findType r i of
     Just (TypeInfo (Just i') k _ ts@(TItype _ t) pkg) -> do
        recordPackageUse pkg
        -- It's a type alias.  If the left element of the alias is a
        -- constructor, find the type of that constructor; otherwise,
        -- give up and return the info that's available.
        case (leftCon t) of
            Just aliased_i -> findTyCon aliased_i
            Nothing -> return (TyCon i' (Just k) ts)
     Just (TypeInfo (Just i') k _ ts pkg) -> do
        recordPackageUse pkg
        return (TyCon i' (Just k) ts)
     Just (TypeInfo Nothing _ _ _ _) ->
        internalError ("findTyCon: unexpected numeric or string type: " ++ ppReadable i)
     Nothing -> errorAtId EUnboundTyCon i

findCls :: CTypeclass -> TI Class
findCls i = do
    r <- getSymTab
    case findSClass r i of
     Just cl -> do
        recordPackageUse (pkg_src cl)
        return cl
     Nothing -> errorAtId EUnboundTyCon (typeclassId i)

bitCls :: TI Class
bitCls = findCls (CTypeclass idBits)

literalCls :: TI Class
literalCls = findCls (CTypeclass idLiteral)

realLiteralCls :: TI Class
realLiteralCls = findCls (CTypeclass idRealLiteral)

sizedLiteralCls :: TI Class
sizedLiteralCls = findCls (CTypeclass idSizedLiteral)

stringLiteralCls :: TI Class
stringLiteralCls = findCls (CTypeclass idStringLiteral)

numEqCls :: TI Class
numEqCls = findCls (CTypeclass idNumEq)

-- Given a field "field_id" encountered in the program (as a field select,
-- a field update, a field definition in a struct literal, or a pattern)
-- and the type "struct_ty" for the struct from the context (possibly just
-- a variable if we don't know anything yet),
-- Returns the type information for that field, if it is able to identify
-- a single field by that name which matches that type.
-- If we know the struct type, then we start with that information.  If
-- the type is only visible internally and is not visible to the user
-- (because it was not imported) or if the fields of the type were not
-- exported with the type, then we want to report those errors first
-- (to maintain the abstraction); if the type does not have a field by
-- that name, then we report that.  Otherwise, if there is not enough
-- type information, we report an error if no field by that name exists,
-- or if multiple fields by that name exist.  If one field by that name
-- is found, then we assume the struct type is that type, and the user
-- will get a mismatch error later if not.
--
findFields :: Type -> Id -> TI (Assump, Id, Int)
findFields struct_ty0 field_id = do
    --traceM("findFields: " ++ ppReadable (struct_ty, field_id))
    symt <- getSymTab

    -- Figure out what we know about the struct type
    -- Return values:
    --    Nothing = Type is not concrete
    --    Just (qtc, isImp, isVis, Nothing)
    --            = Type is not a struct
    --    Just (qtc, isImp, isVis, Just fs)
    --            = Type is a struct
    -- where
    --    qtc   = qualified type name
    --    isImp = whether the data type was imported by the user
    --    isVis = whether the internals of the type were exported
    --    fs    = struct fields
    --
    let getTInfo t =
            case (leftTyCon (expandSyn t)) of
              Nothing -> Nothing
              Just (TyNum n _) -> Just (mkNumId n, True, True, Nothing)
              Just (TyStr s _) -> Just (mkStrId s, True, True, Nothing)
              Just (TyCon tc _ _) ->
                  case (findType symt tc) of
                    Just (TypeInfo (Just qtc) _ _ tcsort _)
                      -> let -- XXX would it be better to compute "isImp"
                             -- XXX by extracting the qualifier and looking
                             -- XXX in the import list?
                             isImp = case (findType symt (unQualId tc)) of
                                       Nothing -> False
                                       Just _  -> True
                             (isVis, tisort_info) = getSortInfo qtc tcsort
                         in  Just (qtc, isImp, isVis, tisort_info)
                    -- We expect it to be a value type
                    -- and we expect that the type has already been checked
                    _ -> internalError ("getTInfo: " ++ ppReadable tc)
        getSortInfo qtc tcsort@(TItype {}) =
            -- this should have been expanded
            internalError ("getSortInfo: " ++ ppReadable tcsort)
        getSortInfo qtc TIabstract =
            -- this should only occur for primitives
            (True, Nothing)
        getSortInfo qtc (TIdata [] _) =
            -- XXX we can't tell if its fields are visible
            (True, Nothing)
        getSortInfo qtc (TIdata (c:_) _) =
            case (findCon symt c) of
              Nothing -> internalError ("getSortInfo findCon: " ++
                                        ppReadable (qtc, c))
              Just cis ->
                  case [ (i, v) | (ConInfo { ci_id = i,
                                             ci_visible = v }) <- cis,
                                   i == qtc ] of
                    [(_, v)] -> (v, Nothing)
                    _ -> internalError ("getSortInfo findCon2: " ++
                                        ppReadable (qtc, c, cis))
        getSortInfo qtc (TIstruct _ []) =
            -- XXX we can't tell if its fields are visible
            (True, Just [])
        getSortInfo qtc (TIstruct _ fs@(f:_)) =
            case (findField symt f) of
              Nothing -> internalError ("getSortInfo findField: " ++
                                        ppReadable (qtc, f))
              Just fis ->
                  case [ (i, v) | (FieldInfo { fi_id = i,
                                               fi_visible = v }) <- fis,
                                   i == qtc ] of
                    [(_, v)] -> (v, Just fs)
                    _ -> internalError ("getSortInfo findField2: " ++
                                        ppReadable (qtc, f, fis))

    s <- getSubst
    let struct_ty = apSub s struct_ty0
    -- internally generated code is allowed to refer to invisible fields
    let ext = not (isInternal field_id)
              -- XXX some internal code is qualified but not marked
              -- XXX so for now allow this (Bug 1858)
              && isUnqualId field_id

    -- now report the error or the info
    case (getTInfo struct_ty) of
      Just (qtc, False, _, _) | ext ->
          err (getIdPosition field_id,
               EFieldsNotImp (pfpString qtc) (getIdQualString qtc))
      Just (qtc, _, False, _) | ext ->
          err (getIdPosition field_id, EFieldsNotVis (pfpString qtc))
      Just (qtc, _, _, Nothing) ->
          -- report the full type, not just the left constructor
          errorAtId (ENotStruct (pfpString struct_ty)) field_id
      Just (qtc, _, _, Just fs) ->
          case (findField symt field_id) of
            Nothing -> errorAtId (ENotField (pfpString qtc)) field_id
            Just fs ->
                case [ (i, a, n, pkg) | (FieldInfo { fi_id = i,
                                                      fi_arity = n,
                                                      fi_assump = a,
                                                      fi_pkg = pkg }) <- fs,
                                        i == qtc ] of
                  [(_, a, n, pkg)] -> do
                      recordPackageUse pkg
                      return (updAssumpPos field_id a, qtc, n)
                  [] -> errorAtId (ENotField (pfpString qtc)) field_id
                  xs -> internalError ("findFields ambig: " ++
                                       ppReadable (struct_ty, field_id, xs))
      Nothing ->
          -- not a concrete type, so we have no type to go on
          case (if ext then findFieldVis else findField) symt field_id of
            Nothing ->
                -- there are no structs with this field
                errorAtId EUnboundField field_id
            Just [FieldInfo {fi_id = qtc, fi_arity = n, fi_assump = a, fi_pkg = pkg }] -> do
                -- there is only one struct with this field
                -- if the expression is not that type, the user will get a
                -- mismatch error later
                recordPackageUse pkg
                return (updAssumpPos field_id a, qtc, n)
            Just fs ->
                let tis = map (pfpString . fi_id) fs
                in  errorAtId (EFieldAmb tis) field_id

updAssumpPos :: Id -> Assump -> Assump
updAssumpPos i (i' :>: s) = setIdPosition (getIdPosition i) i' :>: s


incrementSatStack :: TSSatElement -> TI ()
incrementSatStack x = do
  superstack <- gets tsSatStack
  let oldstack = sizedStackPeek superstack
  flags <- getFlags
  case (sizedStackPush (maxTIStackDepth flags) oldstack x) of
    Nothing -> (err(noPosition,ETypeStackOverflow))
    Just newstack ->
        modify (\ts -> ts { tsSatStack =
                              sizedStackModify superstack (const newstack)})

decrementSatStack :: TI ()
decrementSatStack = do
  superstack <- gets tsSatStack
  modify (\ts -> ts { tsSatStack =
                        sizedStackModify superstack sizedStackPop })

getSatStack :: TI [EPred]
getSatStack = do
  superstack <- gets tsSatStack
  case (sizedStackPeek superstack) of
    (SizedStack _ l) -> return l

pushSatStackContext :: TI ()
pushSatStackContext = do
  superstack <- gets tsSatStack
  flags <- getFlags
  case (sizedStackPush (maxTIStackDepth flags) superstack (mkSizedStack [])) of
    Nothing -> err (noPosition, ETypeSuperStackOverflow)
    Just newstack ->
        modify (\ts -> ts { tsSatStack = newstack })

popSatStackContext :: TI ()
popSatStackContext = do
  superstack <- gets tsSatStack
  modify (\ts -> ts { tsSatStack = (sizedStackPop superstack) })


-- CStruct and CPstruct can be used for either structs fields or
-- constructor fields, and it is up to the typechecker to decide
-- which is intended.
-- Given:
--   * Possible clue from the syntax (True for struct)
--   * Return-type expected by context
--   * Id of the type/constructor
--   * Ids of the fields
-- Returns either Left (for typecheck as struct) or Right (for constr).
--   * Left TyCon  = struct and its type constructor
--   * Right Id    = constructor and the name of its struct arg type
--
disambiguateStruct :: Maybe Bool -> Type -> Id -> [Id] ->
                      TI (Either TyCon Id)
disambiguateStruct mb td c is =
    case mb of
      Just True -> maybeFindTyCon c >>= handleStruct
      Just False -> findCons td c >>= \ (_, ti) -> handleCons (Right ti)
      Nothing -> do
        -- Determine if there is a constructor by this name
        mcons <- maybeFindCons c
        -- Determine if there is a type by this name
        mtype <- maybeFindTyCon c
        -- Attempt to disambiguate
        case (mcons, mtype) of
          (Nothing, _)        -> handleStruct mtype
          (Just mti, Nothing) -> handleCons mti
          (Just (Left _), Just _) ->
            -- XXX we could do more checking, or possibly warn?
            handleStruct mtype
          (Just (Right ti), Just _) -> do
            -- Confirm that the constructor has an SDataCon argument with named fields
            arg_is_cons <- isSDataConNamedM (mkTCId ti c)
            if arg_is_cons
              then -- XXX further check that some of the names match?
                   handleCons (Right ti)
              else handleStruct mtype
 where
   -- Whether a constructor with this name and expected return type exists,
   -- and then either its type or ambiguity errors (if multiple exist)
   maybeFindCons :: Id -> TI (Maybe (Either [EMsg] Id))
   maybeFindCons i =
      let isEConstrAmb (_, EConstrAmb _ _) = True
          isEConstrAmb _ = False
          err_handler es = if all isEConstrAmb (errmsgs es)
                           then return $ Just (Left (errmsgs es))
                           else return $ Nothing
      in  (findCons td i >>= \ (_, ti) -> return (Just (Right ti))) `handle` err_handler

   maybeFindTyCon i =
      (findTyCon i >>= \ tyc -> return (Just tyc)) `handle` \ _ -> return Nothing

   isSDataConNamedM i = do
      mcons <- maybeFindTyCon i
      case mcons of
          Just (TyCon _ _ (TIstruct (SDataCon _ True) fs))
            -> return True
          _ -> return False

   handleCons (Left es) = errs "tiExpr CStruct" es
   handleCons (Right ti) = do
      -- Confirm that the constructor has an SDataCon argument with named fields
      arg_is_cons <- isSDataConNamedM (mkTCId ti c)
      if arg_is_cons
        then return (Right (mkTCId ti c))
        else err (getPosition c, EConstrFieldsNotNamed (pfpString c) (pfpString ti))

   handleStruct (Just tyc@(TyCon c' (Just k) (TIstruct ss qfs))) =
      return (Left tyc)
   handleStruct (Just (TyCon _ _ _)) =
      err (getPosition c, ENotStructId (pfpString c))
   handleStruct _ =
      -- This is the same message that findTyCon would report
      err (getPosition c, EUnboundTyCon (pfpString c))
