module AConv (aConv, aTypeConv, isLocalAId) where

import Util(itos, headOrErr, initOrErr, lastOrErr, log2, concatMapM, makePairs)
import qualified Data.Map as M
import Control.Monad(when, liftM, forM, zipWithM)
import Control.Monad.Except(throwError)
import Control.Monad.State(StateT, runStateT, gets, get, put)
import Control.Monad.Reader(ReaderT, runReaderT, withReaderT, ask)
import PPrint(ppReadable, ppString)
import PFPrint(pfpString)
import Position
import Id
import FStringCompat
import Flags(Flags)
import PreStrings(sSigned)
import PreIds(idBit, idActionValue_, idAVAction_, idAVValue_, idClockOsc, idClockGate,
              idInout_, idPrimArray, idPrimPair, idPrimFst, idPrimSnd, idPrimUnit)
import Pragma
import Error(internalError, EMsg, WMsg, ErrMsg(..),
             ErrorHandle, bsError, bsWarning)
import ISyntax
import ISyntaxUtil
import ITransform(iTransExpr, iTransBoolExpr)
import IntLit(ilDec)
import ASyntax
import ASyntaxUtil
import GenWrapUtils(isGenId, dropGenSuffixId)
import Prim
import Data.List(genericLength, nub)
import Data.Maybe(fromMaybe)
import VModInfo(lookupOutputClockWires, lookupOutputResetWire,
                lookupIfcInoutWire, vArgs, VArgInfo(..))
import SignalNaming
import InstNodes(mkInstTree)

-- import Wires

-- Used by commented-out makeIdMap
--import Data.Char(isDigit)
--import Util(sortGroup)
--import PreStrings(fsUnderscore)

--import Debug.Trace


-- =====
-- Naming conventions

-- XXXX  This will need overhauling

aconvPref :: String
aconvPref = "__d"

-- This is used by AExpand
isLocalAId :: Id -> Bool
isLocalAId i = isBadId i || isFromRHSId i

-- =====

-----
-- Conversion monad.

type CSEMap = M.Map AExpr (AId, AType, AExpr)

type IEDefMap = M.Map Id (AExpr, [DefProp])
data AState = AState {
        errHandle :: ErrorHandle,
        varNo :: !Int, -- for new variable names
        cseMap :: CSEMap, -- for CSE
        stVarMap :: IdMap, -- I-expr names to A-expr names
        ieDefMap :: IEDefMap, -- accumulated definitions
        flags :: Flags, -- to hold the flags on the Monad
        wmsgs :: [WMsg] -- to hold accumulated warnings
        }

type IdMap = M.Map Id Id

type M = ReaderT Bool (StateT AState (Either EMsg))

aInitState :: ErrorHandle -> IdMap -> Flags -> AState
aInitState errh svm flags =
    AState {
             errHandle = errh,
             varNo = 1,
             cseMap = M.empty,
             stVarMap = svm,
             ieDefMap = M.empty,
             flags = flags,
             wmsgs = []
           }

getMap :: M (M.Map AExpr (AId, AType, AExpr))
getMap = liftM cseMap (get)

-- generate an identifier from an expression and add a unique suffix:
-- e.g., x_PLUS_5__d323
newAIdFromAExpr :: Position -> AExpr -> M AId
newAIdFromAExpr p expr = do
        s <- get
        let n = varNo s
            new_name = signalNameFromAExpr expr ++ "_" ++ aconvPref ++ itos n
            new_id = setFromRHSId $ mkId p (mkFString new_name)
            new_id' = if (isSignCast expr)
                      then setSignedId new_id
                      else new_id
        put (s { varNo = n+1 })
        return new_id'
  where isSignCast (AFunCall { ae_funname = name }) = name == sSigned
        isSignCast _ = False

addMap :: AExpr -> AId -> AType -> M ()
addMap e i t = do
        s <- get
        put (s { cseMap = M.insert e (i, t, e) (cseMap s) })

transId :: Id -> M Id
transId i = do s <- get
               return (trId (stVarMap s) i)

getDA :: M IEDefMap
getDA = liftM ieDefMap (get)

addDA :: Id -> AExpr -> [DefProp] -> M ()
addDA i e p = do s <- get
                 -- traceM $ "addDa adding " ++ ppReadable (i,p)
                 put (s { ieDefMap = M.insert i (e,p) (ieDefMap s) })

addWarning :: WMsg -> M ()
addWarning w = do s <- get
                  put (s {wmsgs = w:(wmsgs s)})


getFlags :: M Flags
getFlags = liftM flags (get)

{-
getWMsgs :: M [WMsg]
getWMsgs = M $ \ s -> (s, wmsgs s)
-}

-----

aConv :: ErrorHandle -> [PProp] -> Flags -> IModule a -> IO APackage
aConv errh pps flags imod =
    let itr = makeIdMap (map fst (imod_state_insts imod))
        state = aInitState errh itr flags
    in  case runStateT (runReaderT (aDo imod) False) state of
          Left emsg -> bsError errh [emsg]
          Right (apkg, s) ->
              do
                  let wmessages = wmsgs s
                  when ((not . null) wmessages) $ bsWarning errh wmessages
                  return apkg


-- This checks for methods which are calling tasks or foreign functions.
-- Such calls cannot be guaranteed to output in TRS order, and thus a
-- warning is issued.  This returns a list of offending methods and the
-- positions of task/function calls inside them.
checkForeign :: AIFace -> M [(AId, [Position])]
checkForeign (AIDef { }) = return []
checkForeign (AIClock { }) = return []
checkForeign (AIReset { }) = return []
checkForeign (AIInout { }) = return []
checkForeign a@(AIAction { }) =
    checkForeignInRules (aif_name a) (aif_body a)
checkForeign a@(AIActionValue { }) =
    checkForeignInRules (aif_name a) (aif_body a)

checkForeignInRules :: AId -> [ARule] -> M [(AId, [Position])]
checkForeignInRules method rs =
    let foreign_poss =
            [getPosition i | (ARule { arule_actions = as }) <- rs,
                             (AFCall { aact_objid = i }) <- as] ++
            -- task actions are foreign function calls too
            [getPosition i | (ARule { arule_actions = as }) <- rs,
                             (ATaskAction { aact_objid = i }) <- as]
        filtered_poss = nub $ filter isUsefulPosition foreign_poss
    in  if (not (null foreign_poss))
        then return [(method, filtered_poss)]
        else return []


aDo :: IModule a -> M APackage
aDo imod@(IModule mi fmod be wi ps iks its clks rsts itvs pts idefs rs ifc ffcalNo cmap) = do
        flags <- getFlags

        -- AVInst keeps the types of method ports
        let tsConv :: Id -> [IType] -> ([AType], Maybe AType, [AType])
            tsConv i ts =
                let inputs = initOrErr "tsConv" ts
                    res = lastOrErr "tsConv" ts
                    in_types = map (aTypeConv i) inputs
                    (en_type, val_type)
                      | isitActionValue_ res
                          = (Just (ATBit 1), aTypesConv i (getAV_Type res))
                      | isActionType res
                          = (Just (ATBit 1), [])
                      | otherwise
                          = (Nothing, aTypesConv i res)
                in (in_types, en_type, val_type)

        let (IRules sps irule_list) = rs
        arule_list <- mapM aRule irule_list
        --trace ("aDo rules extracted") $ return ()

        let lookupInstPorts  i = fromMaybe (M.empty) (M.lookup i pts)
        aitvs <- mapM (\ (i0, IStateVar b ui _ v es t tss _ _ hnames) ->
                        do i <- transId i0
                           let portTypes = lookupInstPorts (Just i0)
                           es' <- zipWithM aExprArg (vArgs v) es
                           -- XXX Lennart put a comment here to say "add ifc args in the AVInst list"
                           -- XXX because I think AVerilog filters out fake entries in the AVInst list as ifc args:
                           -- XXX patch in args here
                           return (AVInst (addIdProp i IdPProbe)
                                          (aTypeConv i t)
                                          ui
                                          (map (tsConv i) tss)
                                          portTypes
                                          v
                                          es'
                                          []))
                      itvs

        aifc <- mapM (aIface flags) ifc

        -- Check whether there are any methods calling tasks or foreign funcs,
        -- which need to be warned about
        methodss_to_warn <- mapM checkForeign aifc
        let methods_to_warn = concat methodss_to_warn
            meth_info_digested =
                map (\(i,poss) -> (pfpString i, getPosition i, poss))
                    methods_to_warn
        when (not (null methods_to_warn)) $
            addWarning (getPosition mi, WFCall meth_info_digested)

        -- any defs that have the keepEvenUnused property should be forced
        -- to be kept by calling aEDef to add them to maps in the monad
        -- (the result of aEDef is not needed, just the side effects)
        sequence_ [aEDef i e props | IDef i _ e props <- idefs,
                                     hasIdProp i IdP_keepEvenUnused ]

        defMap <- getDA
        cseMap <- getMap
        -- traceM $ "defMap = " ++ ppReadable defMap
        -- traceM $ "cseMap = " ++ ppReadable cseMap

        -- Restore original names to CSEd definitions, when possible.
        -- But prevent non-CSE defs from becoming CSE'd into other expressions.
        -- Similar to what is being done in ITransform, in iTransFixupDefNames.
        --
        let -- because we use "aSubst" to perform the substitution,
            -- we are doing an Id-to-Expr subst (not Id-to-Id) so we need to
            -- know the type in order to create the ASDef expr
            cse_ids_map :: M.Map AId (AType, [(AId, [DefProp])])
            cse_ids_map =
                let combineFn (t1, ips1) (_, ips2) = (t1, ips1 ++ ips2)
                in  M.fromListWith  combineFn
                        [ (cse_name, (ty, [(def_name, props)]))
                          | (def_name, ((ASDef ty cse_name), props))
                                <- M.toList defMap ]

            rename_map :: M.Map AId (AType, AId)
            rename_map =
                let -- the CSE name was generated with "newAIdFromAExpr"
                    pickId cse_id (ty, def_ips) =
                        -- filter out the non-CSE defs
                        case (filter (not . defPropsHasNoCSE . snd) def_ips) of
                          -- if they're all non-CSE, keep the CSE name
                          [] -> (ty, cse_id)
                          -- otherwise, filter out the bad names
                          names -> case (filter (not . isBadId . fst) names) of
                                     -- if they're all bad, use the CSE name
                                     [] -> (ty, cse_id)
                                     -- otherwise, take the first def name
                                     ((def_id, _):_) -> (ty, def_id)
                in  M.mapWithKey pickId cse_ids_map

            rename_id name = case (M.lookup name rename_map) of
                               Just (_, new_name) -> new_name
                               Nothing -> name

            -- replace refs to CSE'd names with references to the new name
            subst_map :: M.Map AId AExpr
            subst_map =
                let mapFn (ty, new_name) = ASDef ty new_name
                in  M.map mapFn rename_map

        --traceM("rename_map = " ++ ppReadable (M.toList rename_map))
        --traceM("subst_map = " ++ ppReadable (M.toList subst_map))

        let local_defs :: [ADef]
            local_defs =
                let defs_from_cse =
                        -- XXX props are lost on CSE'd defs
                        [ ADef (rename_id i) t (aSubst subst_map e) []
                          | (_, (i, t, e)) <- M.toList cseMap ]
                    non_cse_defs =
                        [ ADef i (ae_type e) (aSubst subst_map e) props
                          | (i, (e, props)) <- M.toList defMap,
                            defPropsHasNoCSE props ]
                in  defs_from_cse ++ non_cse_defs

        reset_list <- mapM (\ir -> do ar <- aReset ir
                                      return (getResetId ir, ar))
                           rsts

        clock_domains <- mapM (\(d, ics) -> do acs <- mapM aClock ics
                                               return (d, acs))
                              clks

        return  (APackage { apkg_name = unQualId (dropGenSuffixId mi),
                            apkg_is_wrapped = fmod,
                            apkg_backend = be,
                            apkg_size_params = [ i | (i, k) <- iks ],
                            apkg_inputs = map aAbstractInput its,
                            apkg_external_wires = wi,
                            apkg_external_wire_types = lookupInstPorts Nothing,
                            apkg_clock_domains = clock_domains,
                            apkg_reset_list = reset_list,
                            apkg_state_instances = aSubst subst_map aitvs,
                            apkg_local_defs = local_defs,
                            apkg_rules = aSubst subst_map arule_list,
                            apkg_schedule_pragmas = sps,
                            apkg_interface = aSubst subst_map aifc,
                            apkg_inst_comments = cmap,
                            apkg_inst_tree = mkInstTree imod,
                            apkg_proof_obligations = [] })

aAbstractInput :: IAbstractInput -> AAbstractInput
aAbstractInput (IAI_Port (i,t)) = (AAI_Port (i, aTypeConv i t))
aAbstractInput (IAI_Clock osc mgate) = (AAI_Clock osc mgate)
aAbstractInput (IAI_Reset r) = (AAI_Reset r)
aAbstractInput (IAI_Inout r n) = (AAI_Inout r n)

aIface :: Flags -> IEFace a -> M AIFace
aIface flags iface@(IEFace i its maybe_e maybe_rs wp fi) = do
        --trace ("enter " ++ ppReadable i) $ return ()
        let its' = [ (arg_i, aTypeConv arg_i arg_t) | (arg_i, arg_t) <- its]
            g = if isRdyId i then aSBool True else ASDef aTBool (mkRdyId i)
        case (maybe_e, maybe_rs) of
          (Nothing, Nothing) -> internalError ("AConv.aIface nothing in it "
                                              ++ ppReadable iface)
          (Just (e, t), Nothing)
            | t == itClock
            -> do
              ac <- case e of
                      ICon _ (ICClock { iClock = c }) -> aClock c
                      _ -> internalError ("AConv.aIface not clock " ++ ppReadable e)
              return $ AIClock i ac fi
            | t == itReset
            -> do
              ar <- case e of
                      ICon _ (ICReset { iReset = r }) -> aReset r
                      _ -> internalError ("AConv.aIFace not reset " ++ ppReadable e)
              return $ AIReset i ar fi
            | isitInout_ t
            -> do
              ar <- case e of
                      ICon _ (ICInout { iInout = r }) -> aInout r
                      _ -> internalError ("AConv.aIFace not inout " ++ ppReadable e)
              return $ AIInout i ar fi
            | t == itAction
              -> internalError ("AConv.aIFace actions should have become rules "
                                ++ ppReadable iface)
            | otherwise
            -> do
              ae <- aExpr e
              return (AIDef i its' wp g (ADef i (aTypeConv i t) ae []) fi [])

          (Nothing, Just rs) -> do
                                   arule_list <- mapM aRule (extractRules rs)
                                   --trace ("exit " ++ ppReadable i) $ return ()
                                   return $ AIAction its' wp g i arule_list fi


          (Just (val_, t), Just rs) -> do
                                   arule_list <- mapM aRule (extractRules rs)
                                   ae <- aExpr val_
                                   --trace ("exit av " ++ ppReadable i) $ return ()
                                   return (AIActionValue its' wp g i arule_list
                                            (ADef i (aTypeConv i t) ae []) fi )
                                   -- should internalError if size(val_)==0 XXX

aRule :: IRule a -> M ARule
aRule (IRule i rps s wp p a orig isl) = do
        --trace ("enter rule " ++ ppReadable i) $ return ()
        p' <- aSExpr p
        as' <- aAction i a
        -- traceM $ "exit rule " ++ ppReadable i
        return (ARule i rps s wp p' as' [] orig)

aReset :: IReset a -> M AReset
aReset r = do
  -- traceM (ppReadable r)
  r' <- case (getResetWire r) of
          IAps (ICon i (ICSel { iConType = itReset })) _ [(ICon vid (ICStateVar {iVar = sv}))] ->
            let i_rstn = lookupOutputResetWire i (getVModInfo sv)
            in  return (mkOutputWire vid i_rstn)
          ICon idNoReset (ICPrim itBit1 PrimResetUnassertedVal) -> do
            return (APrim idNoReset aTBool  PrimResetUnassertedVal [])
          wire_exp -> aSExpr wire_exp
  return (AReset r')

aInout :: IInout a -> M AInout
aInout r = do
  -- traceM (ppReadable r)
  r' <- case (getInoutWire r) of
          e@(IAps (ICon i (ICSel {})) _ [(ICon vid (ICStateVar {iVar = sv}))])
              -> let t = iGetType e
                     i_iot = lookupIfcInoutWire i (getVModInfo sv)
                 in  if (isitInout_ t)
                     then return (mkIfcInoutN (getInout_Size t) vid i_iot)
                     else internalError ("aInout: sel not Inout_ type: " ++
                                         ppReadable e)
          e@(ICon _ (ICModPort t)) ->
              if (isitInout_ t)
              then aSExpr e
              else internalError ("aInout: modport not Inout_ type: " ++
                                  ppReadable e)
          e -> internalError ("aInout: unexpected IExpr: " ++ ppReadable e)
  return (AInout r')

aClock :: IClock a -> M AClock
aClock c = do
  case getClockWires c of
    IAps (ICon _ (ICTuple {fieldIds = [f_osc, f_gate]})) _ [e_osc, e_gate] |
      f_osc == idClockOsc && f_gate == idClockGate -> do
        a_osc  <- aSExpr e_osc
        a_gate <- aSExpr e_gate
        return (AClock { aclock_osc = a_osc, aclock_gate = a_gate })
    -- output clock fields
    IAps (ICon i (ICSel { iConType = itClock })) _ [(ICon vid (ICStateVar {iVar = sv}))] ->
        let (i_osc, mi_gate) = lookupOutputClockWires i (getVModInfo sv)
            osc_aexpr = mkOutputWire vid i_osc
            gate_aexpr = case (mi_gate) of
                             Nothing -> aTrue
                             Just i_gate -> -- mkOutputWire vid i_gate
                                            AMGate aTBool vid i
        in  return (AClock { aclock_osc = osc_aexpr,
                             aclock_gate = gate_aexpr })
    _ -> internalError ("AConv.ASClock: " ++ (show c))

aSExpr :: IExpr a -> M AExpr
aSExpr e = do
        e' <- aExpr e
        noCSE <- ask
        case e' of
         (ASInt _ _ _) -> return e'
         (ASDef _ _) -> return e'
         (ASPort _ _) -> return e'
         (ASParam _ _) -> return e'
         (ASStr _ _ _) -> return e'
         (ASAny _ _) -> return e'
         (ASClock _ _) -> return e'
         (ASReset _ _) -> return e'
         (ASInout _ _) -> return e'
         _ | noCSE -> return e'
         _ -> do
                (i, t, e'') <- find e' (aType e') (getIExprPosition e)
                return (ASDef t i)

aExprArg :: VArgInfo -> IExpr a -> M AExpr
aExprArg (Param _) = aExprNoCSE
aExprArg _         = aExpr

aExprNoCSE :: IExpr a -> M AExpr
aExprNoCSE e = withReaderT (const True) (aExpr e)

aExpr :: IExpr a -> M AExpr
aExpr exp@(IAps (ICon isel (ICPrim _ PrimSelect)) [ITNum i1, ITNum i2, ITNum i3] [e]) = do
        e' <- aSExpr e
        if i2 < i3 && i3-i2 >= i1
           then
            return $ APrim isel (ATBit i1) PrimExtract [e', aNat (i1+i2-1), aNat i2]
           else
            internalError ("aExpr select: bad bit selection\n" ++
                           ppReadable (getIdPosition isel) ++ ppReadable exp)

aExpr (IAps (ICon i (ICPrim _ PrimExtract)) [ITNum i1, _, ITNum i2] [e,h,l]) = do
        let n = log2 i1
        errh <- gets errHandle
        es' <- mapM aSExpr [e, eTrunc errh n h, eTrunc errh n l]
        return $ APrim i (ATBit i2) PrimExtract es'
-- XXX we can remove PrimRange here, or keep it
aExpr (IAps (ICon i (ICPrim _ PrimRange)) _ [_,_,e]) =
        aSExpr e
-- XXX hack to get strings into the compiler (masquerade as integers or bits)
aExpr (IAps (ICon i1 (ICPrim _ PrimIntegerToBit)) _ [IAps (ICon i2 (ICPrim _ PrimStringToInteger)) _ [s]]) =
        aExpr s
-- special cases for sign and zero extensions, since they depend on the type information
aExpr e@(IAps (ICon i (ICPrim _ PrimSignExt)) [_,_,ITNum ii] es) = do
        es' <- mapM aSExpr es
        return $ APrim i (ATBit ii) PrimSignExt es'
aExpr e@(IAps (ICon i (ICPrim _ p)) ts es) | realPrim p = do
        es' <- mapM aSExpr (if p `elem` assocPrims then concatMap (joinOp p) es else es)
        --traceM (ppReadable (es, es'))
        return $ APrim i (primType p ts es') p es'

-- error if "avValue_" is applied to too many arguments
-- (so that the following other case arms can assume this check)
aExpr (IAps (ICon i (ICSel { })) ts (e:es))
    | (i == idAVValue_) && (not (null es))
    = internalError ("aExpr: too many arguments to avValue_: " ++
                     ppReadable es)

aExpr e@(IAps (ICon _ (ICSel {})) _ _) = aSelExpr sels selExpr
    where
      (sels, selExpr) = unfoldICSel e

      unfoldICSel :: IExpr a -> ([(Id, AType)], [IExpr a])
      unfoldICSel e@(IAps (ICon i (ICSel {})) _ [e']) =
          let (sels, a) = unfoldICSel e'
          in  ((i, aTypeConvE e $ iGetType e) : sels, a)
      unfoldICSel e@(IAps (ICon i (ICSel {})) _ a) = ([(i, aTypeConvE e $ iGetType e)], a)
      unfoldICSel e = ([], [e])

aExpr (IAps (ICon _ (ICCon { iConType = ITAp _ t, conTagInfo = cti })) _ _) | t == itBit1 =
        return $ aSBool (conNo cti /= 0)
aExpr e@(IAps (ICon i (ICForeign { fName = name, isC = isC, foports = Nothing})) ts es) = do
        es' <- mapM aSExpr es
        -- XXX should this ever happen?
        -- assume we do not need applied types,
        -- the foreign function is truly polymorphic
        --let ns = [ n | ITNum n <- ts]
        --traceM("AFunCall1: " ++ name)
        return $ AFunCall (aTypeConvE e (iGetType e)) i name isC es'
aExpr e@(IAps (ICon i (ICForeign { fName = name, isC = False, foports = (Just ops)})) ts es) = do
        es' <- mapM aSExpr es
        let ns = [ n | ITNum n <- ts ]
        let t = aTypeConvE e (iGetType e)
            -- because Classic allows foreign functions to be declared,
            -- we need to check if this is a genwrap generated function
            i' = if isGenId i
                 then dropGenSuffixId i
                 else i
        --traceM("AFunCall2: " ++ name)
        return $ ANoInlineFunCall t i'
                   (ANoInlineFun name ns ops Nothing) es'

aExpr e@(IAps (ICon i _) _ _) | i == idPrimPair = do
        let at = aTypeConvE e (iGetType e)
        aes <- aTupleExpr e
        return (ATuple at aes)

aExpr e@(ICon v (ICModPort { iConType = t })) = return (ASPort (aTypeConvE e t) v)
aExpr e@(ICon v (ICModParam { iConType = t })) = return (ASParam (aTypeConvE e t) v)
aExpr e@(ICon v (ICMethArg { iConType = t })) = return (ASPort (aTypeConvE e t) v)
aExpr (ICon i (ICValue { iValDef = e })) = aEDef i e []
-- ^this destroys defprops, add them back with "union" in aEDef.
aExpr e@(ICon id (ICInt { iConType = t, iVal = i })) = return $ ASInt id (aTypeConvE e t) i
aExpr e@(ICon id (ICReal { iConType = t, iReal = r})) = return $ ASReal id (aTypeConvE e t) r
aExpr e@(ICon id (ICString { iConType = t, iStr = s })) = return $ ASStr id (aTypeConvE e t) s
aExpr e@(ICon _ (ICChar { })) =
  internalError ("aExpr: ICChar: " ++ ppReadable e)
aExpr e@(ICon id (ICUndet { iConType = t, iuKind = u, imVal = mv })) | t /= itString = --trace ("ICAny: " ++ ppDebug e) $
  do mv' <- forM mv aSExpr
     return (ASAny (aTypeConvE e t) mv')
aExpr e@(ICon id (ICUndet { iConType = t })) | t == itString =
  throwError (getPosition id, EGeneric "Attempt to use a raw undetermined string")

aExpr e@(ICon i (ICForeign { iConType = t, fName = name, isC = isC, foports = Nothing})) =
        --trace("AFunCall3: " ++ name) $
        return $ AFunCall (aTypeConvE e t) i name isC []
aExpr e@(ICon i (ICForeign { iConType = t, fName = name, isC = False, foports = (Just ops)})) = do
        let i' = if isGenId i
                 then dropGenSuffixId i
                 else i
        --traceM("AFunCall4: " ++ name)
        return $ ANoInlineFunCall (aTypeConvE e t) i'
                   (ANoInlineFun name [] ops Nothing) []
aExpr e@(IAps (ICon _ (ICUndet { })) _ _) =
    internalError ("AConv.ICUndet application " ++ ppReadable e)

aExpr e@(ICon _ (ICClock { iConType = itClock, iClock = c})) = do
  let at = aTypeConvE e itClock
  ac <- aClock c
  return (ASClock at ac)

aExpr e@(ICon _ (ICReset { iConType = t, iReset = r})) =
   do let at = aTypeConvE e t
      ar <- aReset r
      return (ASReset at ar)

aExpr e@(ICon _ (ICInout { iConType = it, iInout = i})) | (isitInout_ it) = do
  let sz = getInout_Size it
      at = aTInout_ sz  -- aTypeConv e it
  ai <- aInout i
  return (ASInout at ai)

aExpr (ICon i _) | i == idPrimUnit = return $ ASInt i (ATBit 0) (ilDec 0)

aExpr e = internalError
              ("AConv.aExpr at " ++ ppString p ++ ":" ++ ppReadable e ++ "\n" ++
               (show p) ++ ":" ++ (showTypeless e))
    where p = getIExprPosition e

aTupleExpr :: IExpr a -> M [AExpr]
aTupleExpr (IAps (ICon i _) [t1, t2] [e1, e2]) | i == idPrimPair = do
        ae1 <- aSExpr e1
        ae2 <- aTupleExpr e2
        return (ae1:ae2)
aTupleExpr e = fmap (:[]) (aSExpr e)

aSelExpr :: [(Id, AType)] -> [IExpr a] -> M AExpr

-- value part of ActionValue task without arguments
aSelExpr [(m, t)] [(ICon i (ICForeign {fName = name,
                                       isC = isC,
                                       foports = Nothing,
                                       fcallNo = mn}))]
    | m == idAVValue_ =
    let n = case (mn) of
                Nothing -> internalError
                               ("aExpr: avValue_ on ICForeign without fcallNo")
                Just val -> val
    in
        return (ATaskValue t i name isC n)

-- value part of ActionValue task with arguments
aSelExpr [(m, t)] [(IAps (ICon i (ICForeign {fName = name,
                                             isC = isC,
                                             foports = Nothing,
                                             fcallNo = mn})) fts fes)]
    | m == idAVValue_ =
    let n = case (mn) of
                Nothing -> internalError
                               ("aExpr: avValue_ on ICForeign without fcallNo")
                Just val -> val
    in
        -- the value side carries no arguments
        -- the cookie "n" will connect it back up to the action side
        return (ATaskValue t i name isC n)

-- port selected from value part of ActionValue method
aSelExpr ((sel, atype) : sels) base@(ICon i (ICStateVar { }) : es)
    | (sel == idPrimFst || sel == idPrimSnd)
    , [(iav, atypeTup), (m, _)] <- dropWhile ((== idPrimSnd) . fst) sels = do
  i' <- transId i
  -- arguments should have been dropped in IExpand
  when (not (null es)) $
      internalError ("AConv.aExpr actionvalue value with args " ++
                     ppReadable sels ++ "\n" ++ ppReadable base)
  let idx = toInteger $ (if sel == idPrimSnd then 1 else 0) + length sels - 2
  return $ ATupleSel atype (AMethValue atypeTup i' m) $ idx + 1

-- port selected from value method
aSelExpr ((sel, atype) : sels) (ICon i (ICStateVar { }) : es)
    | (sel == idPrimFst || sel == idPrimSnd)
    , [(m, atypeTup)] <- dropWhile ((== idPrimSnd) . fst) sels = do
  i' <- transId i
  es' <- mapM aSExpr es
  let idx = toInteger $ (if sel == idPrimSnd then 1 else 0) + length sels - 1
  return $ ATupleSel atype (AMethCall atypeTup i' m es') $ idx + 1

-- value part of ActionValue method
aSelExpr sels@[(iav, atype), (m, _)] base@(ICon i (ICStateVar { }) : es)
    | (iav == idAVValue_) = do
  i' <- transId i
  -- arguments should have been dropped in IExpand
  when (not (null es)) $
      internalError ("AConv.aExpr actionvalue value with args " ++
                     ppReadable sels ++ "\n" ++ ppReadable base)
  -- IExpand is failing to optimize away bit-zero results from methods
  -- and foreign functions, so catch that here for ActionValue methods
  return $ if (atype == aTZero)
           then ASInt i (ATBit 0) (ilDec 0)
           else AMethValue atype i' m

-- value method
aSelExpr [(m, atype)] (ICon i (ICStateVar { }) : es) = do
  i' <- transId i
  es' <- mapM aSExpr es
  return $ AMethCall atype i' m es'

aSelExpr [(m, _)] [ICon i (ICClock { iClock = c })] | m == idClockGate = do
        ac <- aClock c
        return (aclock_gate ac)
-- XXX This is here because aClock calls aSExpr on the oscillator.  However,
-- XXX that should be the only place where an osc ever appears in an expr.
aSelExpr [(m, _)] [ICon i (ICClock { iClock = c })] | m == idClockOsc = do
        ac <- aClock c
        return (aclock_osc ac)

aSelExpr sels base = internalError
              ("AConv.aSelExpr:" ++
               ppReadable sels ++ "\n" ++ ppReadable base)


aEDef :: Id -> IExpr a -> [DefProp] -> M AExpr
aEDef i e ps = do
        da <- getDA
        -- traceM $ "aEDef " ++ ppReadable (i,e,ps)
        case M.lookup i da of
         Just (a, _) -> do
           return a
         Nothing -> do
            -- traceM $ "not found"
            a <- aSExpr e
            addDA i a ps
            return a

aTypeConv :: Id -> IType -> AType
aTypeConv _ (ITAp (ITCon b _ _) (ITNum n)) | b == idBit = ATBit n
aTypeConv _ (ITAp (ITCon i _ _) (ITNum n)) | i == idInout_ = ATAbstract idInout_ [n]
aTypeConv a (ITAp (ITCon r _ _) elem_ty) | r == idPrimArray =
    -- no way to get the size
    internalError("aTypeConv: array: " ++ ppReadable a)
aTypeConv a t@(ITAp (ITAp (ITCon p _ _) _) _) | p == idPrimPair =
  ATTuple (aTypesConv a t)
aTypeConv _ t | t == itReal = ATReal
aTypeConv _ t | t == itString = ATString Nothing
-- Deal with AVs
aTypeConv a (ITAp (ITCon i _ _) t) | i == idActionValue_ =
    aTypeConv a t
aTypeConv a (ITCon i _ _) | i == idPrimUnit = ATBit 0
aTypeConv _ t = abs t []
  where abs (ITCon i _ _) ns = ATAbstract i (reverse ns)
        abs (ITAp t _) ns = abs t ns
        abs _ _ = -- ATAbstract idBit []        -- XXX what's this
                  internalError ("aTypeConv|" ++ show t)

-- This is a variation of "aTypeConv" that is only used by "aExpr".
-- A String expression can be used to determine the size of the ATString type.
--
aTypeConvE :: IExpr a -> IType -> AType
aTypeConvE a (ITAp (ITCon b _ _) (ITNum n)) | b == idBit = ATBit n
aTypeConvE a (ITAp (ITCon i _ _) (ITNum n)) | i == idInout_ = ATAbstract idInout_ [n]
aTypeConvE a (ITAp (ITCon r _ _) elem_ty) | r == idPrimArray =
  -- XXX we could examine the expression and find the type
  -- XXX but this func isn't used to get the type of PrimBuildArray
  internalError ("aTypeConv: array: " ++ ppReadable a)
aTypeConvE _ t@(ITAp (ITAp (ITCon p _ _) _) _) | p == idPrimPair =
  ATTuple (aTypesConv p t)
aTypeConvE a t | t == itReal = ATReal
aTypeConvE a t | t == itString =
  case a of
    (ICon _ (ICString _ s)) -> ATString (Just (genericLength s))
    otherwise               -> ATString Nothing
aTypeConvE a (ITCon i _ _) | i == idPrimUnit = ATBit 0
aTypeConvE a t = abs t []
  where abs (ITCon i _ _) ns = ATAbstract i (reverse ns)
        abs (ITAp t _) ns = abs t ns
        abs _ _ = -- ATAbstract idBit []        -- XXX what's this
                  internalError ("aTypeConvE|" ++ show t)

aTypesConv :: Id -> IType -> [AType]
aTypesConv a (ITAp (ITAp (ITCon p _ _) t1) t2) | p == idPrimPair =
  aTypeConv a t1 : aTypesConv a t2
aTypesConv a t = [aTypeConv a t]

realPrim :: PrimOp -> Bool
realPrim p = p `elem`
        [
         PrimSignExt, PrimZeroExt, PrimTrunc,
         PrimExtract, PrimConcat,
         PrimIf, PrimCase,
         PrimBuildArray, PrimArrayDynSelect,
         PrimRange,
         -- not primArith because not Bit n -> Bit n -> Bit n
         PrimMul, PrimQuot, PrimRem
        ] ++ primAriths ++ primCmps ++ primBools ++ primStrings
primAriths :: [PrimOp]
primAriths = [ PrimAdd, PrimSub, PrimAnd, PrimOr, PrimXor,
               PrimSL, PrimSRL, PrimSRA,
               PrimInv, PrimNeg ]
primBools :: [PrimOp]
primBools = [ PrimBAnd, PrimBOr, PrimBNot ]
primCmps :: [PrimOp]
primCmps = [ PrimEQ, PrimEQ3,
             PrimULE, PrimULT,
             PrimSLE, PrimSLT ]
primStrings :: [PrimOp]
primStrings = [ PrimStringConcat ]

-- Many primops are associative, but if we reassociate we might rebalance a carefully
-- set up tree of computations.
--assocPrims = [ PrimAdd, PrimAnd, PrimOr, PrimXor, PrimConcat, PrimBAnd, PrimBOr ]
assocPrims :: [PrimOp]
assocPrims = [ PrimConcat ]

joinOp :: PrimOp -> IExpr a -> [IExpr a]
joinOp p (IAps (ICon _ (ICPrim { primOp = p' })) _ es) | p == p' = es
joinOp _ e = [e]

sumStrSizes :: [AExpr] -> Maybe ASize
sumStrSizes []     = Just 0
sumStrSizes (e:es) = do n  <- case (aType e) of
                                (ATString sz) -> sz
                                otherwise       -> Nothing
                        n' <- sumStrSizes es
                        return (n + n')

{-
aPrim :: AType -> PrimOp -> AExpr -> AExpr
aPrim t p es | p `elem` assocPrims = APrim _ t p (concatMap join es)
  where join (APrim _ t' p' es) | t == t' && p == p' = es
        join e = [e]
aPrim t p es = APrim _ t p es
-}

-- Rather than have a separate arm of aExpr for every PrimOp,
-- we have one general arm that uses this function to determine the type
--
primType :: PrimOp -> [IType] -> [AExpr] -> AType
primType PrimIf _ [_, e2, e3] =
    let t2 = aType e2
        t3 = aType e3
    in  if (isStringType t2)
        then unifyStringTypes [t2, t3]
        else t2
primType PrimCase _ (_:d:ps) =
    let ces = makePairs ps
        arm_ts = map (aType . snd) ces
        dflt_t = aType d
    in  if (isStringType dflt_t)
        then unifyStringTypes (dflt_t:arm_ts)
        else dflt_t
primType PrimConcat _ es = ATBit (sum (map (unbit . aType) es))
    where unbit (ATBit width) = width
          unbit _ = internalError "concatenation of abstract types in AConv.primType"
primType PrimMul ts _ = ATBit (getNum (last ts))
    where getNum (ITNum n) = n
          getNum _ = internalError "multiplication of abstract types in AConv.primType"
primType PrimQuot ts _ = ATBit (getNum (head ts))
    where getNum (ITNum n) = n
          getNum _ = internalError "quotient of abstract types in AConv.primType"
primType PrimRem ts _ = ATBit (getNum (last ts))
    where getNum (ITNum n) = n
          getNum _ = internalError "remainder of abstract types in AConv.primType"
primType p _ _ | p `elem` (primBools ++ primCmps) = ATBit 1
primType p _ (e:_) | p `elem` primAriths || p == PrimRange = aType e
primType (PrimStringConcat) _ es@(_:_) = ATString (sumStrSizes es)
primType PrimBuildArray _ es =
    let sz = genericLength es
        ts = map aType es
        t0 = headOrErr "AConv.primType: size zero array" ts
        elem_ty = if (isStringType t0)
                  then unifyStringTypes ts
                  else t0
    in  ATArray sz elem_ty
primType PrimArrayDynSelect _ (arr:_) =
    case (aType arr) of
      ATArray _ t -> t
      _ -> internalError ("primType: array select: " ++ ppReadable arr)
primType p ts xs = internalError ("primType " ++ ppReadable (p, ts, xs))

aAction :: ARuleId -> IExpr a -> M [AAction]
aAction s a = aAction' s iTrue a

aAction' :: ARuleId -> IExpr a -> IExpr a -> M [AAction]
aAction' s cond a = do
   result <- mapM (aAction1 s cond) (flatAction a)
   return (concat result)

aAction1 :: ARuleId -> IExpr a -> IExpr a -> M [AAction]
-- A hack to handle polymorphic methods (e.g. printBit)
aAction1 r cond (IAps (IAps f _ es1) _ es2) = aAction1 r cond (IAps f [] (es1++es2))

-- action part of ActionValue task without arguments
aAction1 _ cond a@(IAps (ICon avAction_ (ICSel { })) _
                        ((ICon i (ICForeign {iConType = ity,
                                             fName = name,
                                             isC = isC,
                                             foports = Nothing,
                                             fcallNo = mn})) : es))
   | avAction_ == idAVAction_ = do
   let n = case (mn) of
              Nothing -> internalError
                           ("aAction1: avAction_ on ICForeign without fcallNo")
              Just val -> val
       value_type = aTypeConv i (snd (itGetArrows ity))
   when (not (null es)) $
       internalError ("aAction1: too many arguments to avAction_: " ++
                      ppReadable es)
   cond' <- aSExpr cond
   return [(ATaskAction i name isC n [cond'] Nothing value_type False)]

-- action part of ActionValue task with arguments
aAction1 _ cond a@(IAps (ICon avAction_ (ICSel { })) _
                        ((IAps (ICon i (ICForeign {iConType = ity0,
                                                   fName = name,
                                                   isC = isC,
                                                   foports = Nothing,
                                                   fcallNo = mn})) fts fes) : es))
   | avAction_ == idAVAction_ = do
   let n = case (mn) of
              Nothing -> internalError
                           ("aAction1: avAction_ on ICForeign without fcallNo")
              Just val -> val
       -- allow for polymorphic foreign functions
       ity = itInst ity0 fts
       value_type = aTypeConv i (snd (itGetArrows ity))
   when (not (null es)) $
       internalError ("aAction1: too many arguments to avAction_: " ++
                      ppReadable es)
   cond' <- aSExpr cond
   fes'   <- mapM aSExpr fes
   return [(ATaskAction i name isC n (cond' : fes') Nothing value_type False)]

aAction1 r cond a@(IAps (ICon avAction_ (ICSel { })) _ es) | avAction_ == idAVAction_ =
   case es of
       -- if the selection is on a method call, then recurse on the method call
       [e@(IAps (ICon m (ICSel { })) _ (ICon i (ICStateVar { }) : method_es))]
           -> aAction1 r cond e
       -- anything else is invalid
       [e] -> internalError
               ("aAction1: avAction_ called on non-primitive actionvalue\n" ++
                "e = " ++ show e)
       _ -> internalError "aAction1: avAction_ with wrong number of arguments"

aAction1 _ cond (IAps (ICon m (ICSel { })) _ (ICon i (ICStateVar { }) : es)) = do
        cond' <- aSExpr cond
        es' <- mapM aSExpr es
        i' <- transId i
        return [ACall i' m (cond' : es')]

aAction1 _ cond (IAps (ICon i (ICForeign { fName = name, isC = isC, foports = Nothing })) ts es) = do
        cond' <- aSExpr cond
        es' <- mapM aSExpr es
        -- XXX should this ever happen?
        -- assume we do not need applied types,
        -- the foreign function is truly polymorphic
        --let ns = [ n | ITNum n <- ts ]
        return [AFCall i name isC (cond' : es') False]

-- noinline functions returning Action are not synthesizable, so this
-- branch is not needed
--aAction1 _ cond (IAps (ICon i (ICForeign { fName = name, isC = False, foports = Just ops })) ts es) = ...

-- special case for 0 argument foreign calls
aAction1 _ cond (ICon i (ICForeign { fName = name, isC = isC, foports = Nothing })) = do
        cond' <- aSExpr cond
        return [AFCall i name isC [cond'] False]

aAction1 s cond (IAps (ICon _ (ICPrim { primOp = PrimIf })) _ [c, t, e]) = do
        flags <- getFlags
        t' <- aAction' s (iTransBoolExpr flags (c `ieAnd` cond)) t
        e' <- aAction' s (iTransBoolExpr flags ((ieNot c) `ieAnd` cond)) e
        return (t' ++ e')

{-
aAction1 s cond (ICon _ (ICPrim { primOp = PrimNoActions })) =
        return ([])
-}

-- XXX find a way to preserve the array in AAction
aAction1 s cond
    (IAps ic@(ICon i_sel (ICPrim { primOp = PrimArrayDynSelect }))
          ts@[_, idx_sz_ty@(ITNum idx_sz)]
          [e_arr, e_idx]) =
  case e_arr of
    (ICon i (ICValue { iValDef = e_arr' })) ->
        aAction1 s cond (IAps ic ts [e_arr', e_idx])
    (IAps (ICon _ (ICPrim { primOp = PrimBuildArray })) _ elem_es) -> do
        flags <- getFlags
        let ty_idx = aitBit idx_sz_ty
        -- number of arms is the min of the elems and the max index
        let max_idx = (2^idx_sz) - 1
            ncells = zip [0..max_idx] elem_es
        let mapFn (n, e_cell) = do
              let n_lit = iMkLitAt (getPosition i_sel) ty_idx n
                  c = iePrimEQ idx_sz_ty e_idx n_lit
              aAction' s (iTransBoolExpr flags (c `ieAnd` cond)) e_cell
        -- We assume that the default for out of range indexes is noAction
        concatMapM mapFn ncells
    _ -> internalError ("aAction1: unexpected array: " ++ ppReadable e_arr)

--aAction1 r cond e = internalError ("aAction1: " ++ ppReadable (r, cond, e))
-- for deeper tracing
aAction1 r cond e = internalError ("aAction1 end: " ++ ppReadable (r, cond, e) ++ "\n" ++ showTypeless e)

find :: AExpr -> AType -> Position -> M (AId, AType, AExpr)
find e t pos = do
        m <- getMap
        case M.lookup e m of
         Just ite -> return ite
         Nothing -> do
                i <- newAIdFromAExpr pos e
                addMap e i t
                return (i, t, e)

-----

extractRules :: IRules a -> [IRule a]
extractRules (IRules sps rs) = rs

-----

-- #############################################################################
-- # The renaming has been moved to IEXpand so this can become an
-- # identity map now.
-- #############################################################################


makeIdMap :: [Id] -> IdMap
makeIdMap ids = M.fromList (zip ids ids)

-- makeIdMap :: [Id] -> IdMap
-- makeIdMap = M.fromList . concatMap numGroup . sortGroup le
--   where le i1 i2 = nonum (getIdString i1) <= nonum (getIdString i2)
--         nonum = reverse . tail . dropWhile isDigit . reverse
--         numGroup [i] = [(i, noNumId i)]
--         numGroup is = zipWith (\ i n -> (i, mkIdPost (noNumId i) (concatFString [fsUnderscore, mkNumFString n]))) is [0..]
--         noNumId i = mkId (getIdPosition i) (mkFString (nonum (getIdString i)))

trId :: IdMap -> Id -> Id
trId m i =
    case M.lookup i m of
    Just i' -> setIdPosition (getIdPosition i) i'
    Nothing -> internalError ("trId " ++ ppReadable i)

-----

-- XXX should insert runtime-error code when we truncate the indices on PrimExtract
eTrunc :: ErrorHandle -> ASize -> IExpr a -> IExpr a
eTrunc errh n e =
    if (k > n)
    then let e' = IAps (icSelect noPosition) [ITNum n, ITNum 0, ITNum k] [e]
         in  fst (iTransExpr errh e')
    else e
  where k = case aTypeConvE e (iGetType e) of
              ATBit sz -> sz
              _ -> internalError "AConv.eTrunc: unexpected type"
