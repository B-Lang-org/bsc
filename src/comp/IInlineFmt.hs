module IInlineFmt(iInlineFmt) where
import PPrint
import ErrorUtil
import ISyntax
import IInlineUtil(iSubstIfc, iSubstWhen)
import ISyntaxUtil(itString, icJoinActions, itBit, irulesMap, irulesMapM, itFmt, itGetArrows, itFun, itInst, itAction, iGetType, joinActions, iMkString, isitAction, isitActionValue_, iDefMapM, iDefsMap, emptyFmt)
import Id
import Prim
import PreIds(idActionValue_, idArrow, tmpVarIds, idAVValue_, idAVAction_, idPrimFmtConcat)
import ForeignFunctions
import Control.Monad.Except(ExceptT, runExceptT)
import Control.Monad.State
import Error(EMsg, ErrorHandle, bsError)
import Position(noPosition)
import CType(TISort(..), StructSubType(..))
import qualified Data.Map as M
-- import Debug.Trace(trace)

type F a = StateT (Int, [IDef a]) (ExceptT EMsg (IO))

newFFCallNo :: (F a) Integer
newFFCallNo = do (n, ds) <- get
                 put ((n + 1), ds)
                 return (toInteger n)

addDefs :: [IDef a] -> (F a) ()
addDefs ds = do (n, ds') <- get
                put (n, ds' ++ ds)
                return ()

-- #############################################################################
-- #
-- #############################################################################

iInlineFmt :: ErrorHandle -> IModule a -> IO (IModule a)
iInlineFmt errh imod =
    do let imod_fmt = iInlineFmts imod
       let ffcallNo = (imod_ffcallNo imod_fmt)
       let ds       = (imod_local_defs imod_fmt)
       result <- runExceptT (runStateT (splitFmtsF imod_fmt) (ffcallNo, []))
       case result of
            Right x@(imod', (ffcallNo', ds')) ->
                return (imod' {imod_local_defs = ds ++ ds',
                               imod_ffcallNo = ffcallNo'})
            Left msg -> bsError errh [msg]

splitFmtsF :: IModule a -> F a (IModule a)
splitFmtsF imod@(IModule { imod_local_defs  = ds,
                           imod_rules       = rs,
                           imod_interface   = ifc,
                           imod_state_insts = state_vars}) =
    do  let ds' = [ IDef id t e p | IDef id t e p <- ds, (t /= itFmt) ] -- remove (now unused defs)
            updateDef = iDefMapM ssplitFmt
        ds'' <- mapM updateDef ds'

        ifc' <- ssplitFmt_ifc ifc
        rs'  <- irulesMapM ssplitFmt rs
        let updateStateVar (name, sv@(IStateVar { isv_iargs = es })) = do es' <- mapM ssplitFmt es
                                                                          return (name, sv { isv_iargs = es' })
        state_vars' <- mapM updateStateVar (imod_state_insts imod)
        return imod { imod_local_defs  = ds'',
                      imod_rules       = rs',
                      imod_interface   = ifc',
                      imod_state_insts = state_vars' }

ssplitFmt :: IExpr a -> F a (IExpr a)
ssplitFmt e =
    do expr' <- fsplitFmt e
       splitFmt expr'

--------------------------------------------------------------------------------
-- Special handling for $fdisplay, $fwrite etc.
-- 1) Remove first arg (the file descriptor)
-- 2) Do split processing as usual
-- 3) Add first arg back to all the "descendant" foreign functions.
--------------------------------------------------------------------------------
fsplitFmt :: IExpr a -> F a (IExpr a)
fsplitFmt (IAps (ICon fid f@(ICForeign {iConType = t})) [] (e:rest))
              | isFileId fid  =
    do  expr' <- splitFmt (IAps (ICon fid f {iConType = t'}) [] rest)
        return (addFileArg e expr')
    where (_ , rt) = itGetArrows (getInnerType t)
          at'      = map iGetType rest
          t'       = foldr1 itFun (at' ++ [rt])
fsplitFmt (IAps x ts es) =
    do  es' <- mapM fsplitFmt es
        return (IAps x ts es')
fsplitFmt x = return x

addFileArg :: IExpr a -> IExpr a -> IExpr a
addFileArg e (IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
             | isFileId fid = (IAps (ICon fid f {iConType = t'}) [] es')
    where (_ , rt) = itGetArrows (getInnerType t)
          es'      = e : es
          at'      = map iGetType es'
          t'       = foldr1 itFun (at' ++ [rt])
addFileArg e (IAps x ts es) = (IAps x ts (map (addFileArg e) es))
addFileArg e x              = x

splitFmt :: IExpr a -> F a (IExpr a)
splitFmt e =
  do let e0 = replaceDisplays e
     e1 <- unNestFmts [] [] e0
     let e2 = combineFmts e1
         e3 = promoteConcat False e2
     e4 <- splitFF True [] [] e3
     e5 <- removeConcat e4
     return e5;
  where -- first turn any $display (and friends) calls into $write (and friends) calls
        -- but only if there are arguments of type Fmt ... leave the rest alone
        replaceDisplays (IAps (ICon fid f@(ICForeign {iConType = t})) _ es)
                         | isDisplayId(fid) && (any (== itFmt) at) = expr
               where (_ , rt) = itGetArrows (getInnerType t)
                     at       = map iGetType es
                     fid'     = fromDisplayId fid
                     name'    = getIdString(unQualId(fid'))
                     es'      = es ++ [iMkString "\n"]
                     at'      = map iGetType es'
                     t'       = foldr1 itFun (at' ++ [rt])
                     expr = (IAps (ICon fid' f {fName = name', iConType = t'}) [] es')
        replaceDisplays (IAps x ts es) = (IAps x ts (map replaceDisplays es))
        replaceDisplays x = x

        -- eliminated nested Fmts (replace with primFmtConcat ops).
        -- after this step all $formats are leaves
        -- top down processing
        unNestFmts _   _         (IAps (ICon _ (ICForeign {iConType = t})) [] [e])
                         | iGetType e == itFmt && rt == itFmt =
               do e' <- unNestFmts [] [] e
                  return e'
               where (_ , rt) = itGetArrows (getInnerType t)
        unNestFmts []  []      x@(IAps (ICon _ (ICForeign {iConType = t})) [] es@(e:rest))
                         | rt == itFmt =
               do e' <- unNestFmts [e] rest x
                  return e'
               where (_ , rt) = itGetArrows (getInnerType t)
        unNestFmts es0 []      x@(IAps (ICon _ (ICForeign {iConType = t})) [] es@(e:rest))
                         | rt == itFmt = return x
               where (_ , rt) = itGetArrows (getInnerType t)
        unNestFmts es0 (e:rest)  (IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
                         | iGetType e == itFmt && rt == itFmt =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- unNestFmts [] [] (IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)
                  e1 <- unNestFmts [] [] (IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] (e:rest))
                  return (IAps (ICon idPrimFmtConcat (ICPrim tc PrimFmtConcat)) [] [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType (e:rest)
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
                     tc       = foldr1 itFun [itFmt, itFmt, itFmt]
        unNestFmts es0@(e:rest) es1 (IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
                         | iGetType (last es0) == itFmt && rt == itFmt =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- unNestFmts [] [] (IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)
                  e1 <- unNestFmts [] [] (IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] es1)
                  return (IAps (ICon idPrimFmtConcat (ICPrim tc PrimFmtConcat)) [] [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType es1
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
                     tc       = foldr1 itFun [itFmt, itFmt, itFmt]
        unNestFmts es0 (e:rest) x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es) =
               do e' <- unNestFmts (es0 ++ [e]) rest x
                  return e'
        unNestFmts es0 es1      (IAps x ts es) =
               do es' <- mapM (unNestFmts es0 es1) es
                  return (IAps x ts es')
        unNestFmts _   _      x  = return x

        combineFmts (IAps (ICon _ (ICPrim _ PrimFmtConcat)) _
                     [(IAps (ICon fid f@(ICForeign {iConType = t})) ts0 es0),
                      (IAps (ICon _     (ICForeign {})) ts1 es1)]) =
           let es = (es0 ++ es1)
               ts = (map iGetType es)
               (_ , rt) = itGetArrows (getInnerType t)
               tc = foldr1 itFun (ts ++ [rt])
               e = (IAps (ICon fid f {iConType = tc}) [] es)
           in e
        combineFmts (IAps c ts es) =
           let es' = map combineFmts es
           in (IAps c ts es')
        combineFmts e = e

        -- next move primFmtConcats up so that after this step, all the primFmtConcats in any
        -- expression come first
        -- bottom up processing
        promoteConcat r (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti es@[cond, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e0, e1]), e2]) =
          promoteConcat False (IAps cc tc [(IAps ci ti [cond, e0, e2]), (IAps ci ti [cond, e1, emptyFmt])])
        promoteConcat r (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e2, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e0, e1])]) =
          promoteConcat False (IAps cc tc [(IAps ci ti [cond, e2, e0]), (IAps ci ti [cond, emptyFmt, e1])])
        promoteConcat False (IAps x@(ICon _ (ICForeign {})) ts es) =
          IAps x ts (map (promoteConcat False) es)
        promoteConcat False (IAps x ts es) =
          promoteConcat True (IAps x ts (map (promoteConcat False) es))
        promoteConcat _ x = x

        -- next the first phase of action-ff splitting
        -- all action-ff calls (which include Fmt arguments) are split
        -- into multiple ff calls (along the Fmt argument boundaries)
        splitFF d _   _       x@(IAps (ICon _ (ICForeign {iConType = t})) [] [e])
                         | iGetType e == itFmt && rt == itFmt =
               splitFF d [] [] e
               where (_ , rt) = itGetArrows (getInnerType t)
        splitFF d []  []      x@(IAps (ICon _ (ICForeign {iConType = t})) [] es@(e:rest))
                         | isActionFFWithFmts x =
               do x' <- splitFF d [e] rest x
                  x''  <- removeConcat x'
                  x''' <- reduceFmt x''
                  return x'''
        splitFF d []  []   y@(IAps cc@(ICon i s@(ICSel {iConType = t'})) ts [x@(IAps (ICon fid ff@(ICForeign {iConType = t})) [] es@(e:rest))])
                         | isAVFFWithFmts x && rt' == itAction =
               do x'    <- splitFF d [e] rest y
                  x''   <- removeConcat x'
                  x'''  <- reduceFmt x''
                  x'''' <- update d x'''
                  return x''''
              where (_ , rt)  = itGetArrows (getInnerType t)
                    (_ , rt') = itGetArrows (getInnerType t')
                    update False r                            = return r
                    update _     r@(IAps icJoinActions _ [e]) = return r
                    update _     r@(IAps c _ ees) | c == icJoinActions  =
                     do addDefs defs
                        return (joinActions [r', f])
                     where f            = (IAps cc ts [(IAps (ICon fid ff {iConType = t''}) [] args)])
                           vs           = concatMap createValueExprs ees
                           tconcat (xs, ys, zs) = (concat xs, concat ys, concat zs)
                           (refs, defs, as) = tconcat (unzip3 (map createRefsAndDefsAndActions vs))
                           r'   = joinActions as
                           args        = refs
                           at''        = map iGetType args
                           t''  = foldr1 itFun (at'' ++ [rt])
                    update _     r                            = return r
        splitFF _ es0 []      x@(IAps (ICon _ (ICForeign {iConType = t})) [] es@(e:rest))
                         | rt == itAction =
               return x
               where (_ , rt) = itGetArrows (getInnerType t)
        splitFF _ es0  []   y@(IAps (ICon _ (ICSel {iConType = t'})) _ [x@(IAps (ICon _ (ICForeign {iConType = t})) [] es@(e:rest))])
                         | isAVFFWithFmts x && rt' == itAction =
               return y
               where (_ , rt') = itGetArrows (getInnerType t')
        splitFF _ es0 (e:rest)  x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
                         | iGetType e == itFmt =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- splitFF False [] [] (IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)
                  e1 <- splitFF False [] [] (IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] (e:rest))
                  return (joinActions [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType (e:rest)
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
        splitFF _ es0 (e:rest)   (IAps c@(ICon _ (ICSel {})) ts [x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es)])
                         | iGetType e == itFmt =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- splitFF False [] [] (IAps c ts [(IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)])
                  e1 <- splitFF False [] [] (IAps c ts [(IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] (e:rest))])
                  return (joinActions [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType (e:rest)
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
        splitFF _ es0@(e:rest) es1 x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
                         | iGetType (last es0) == itFmt && isActionFFWithFmts x =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- splitFF False [] [] (IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)
                  e1 <- splitFF False [] [] (IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] es1)
                  return (joinActions [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType es1
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
        splitFF _ es0@(e:rest) es1 (IAps c@(ICon _ (ICSel {})) ts [x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es)])
                         | iGetType (last es0) == itFmt =
               do n0 <- newFFCallNo
                  n1 <- newFFCallNo
                  e0 <- splitFF False [] [] (IAps c ts [(IAps (ICon fid f {fcallNo = (Just n0), iConType = t'})  [] es0)])
                  e1 <- splitFF False [] [] (IAps c ts [(IAps (ICon fid f {fcallNo = (Just n1), iConType = t''}) [] es1)])
                  return (joinActions [e0, e1])
               where (_ , rt) = itGetArrows (getInnerType t)
                     at'      = map iGetType es0
                     at''     = map iGetType es1
                     t'       = foldr1 itFun (at' ++ [rt])
                     t''      = foldr1 itFun (at'' ++ [rt])
        splitFF d es0 (e:rest) x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] es) =
               splitFF d (es0 ++ [e]) rest x
        splitFF d es0 (e:rest) x@(IAps c@(ICon _ (ICSel {})) ts [(IAps (ICon fid f@(ICForeign {iConType = t})) [] es)]) =
               splitFF d (es0 ++ [e]) rest x
        splitFF d es0 es1      (IAps x ts es) =
               do es' <- mapM (splitFF d es0 es1) es
                  return (IAps x ts es')
        splitFF _ _   _      x  =  return x

        -- At this point, all Fmt types in action-ff will be the only argument

        -- we find those single argument action-ff calls, eliminate
        -- all the primFmtConcats from the associated fmt expression,
        -- and split the associated action-ff in the process
        -- top down processing
        removeConcat x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] [e])
                                 | iGetType e == itFmt && isActionFFWithFmts x =
               do action_list <- mapM mkFF listoflists
                  return (joinActions action_list)
               where (_ , rt)    = itGetArrows (getInnerType t)
                     mkFF es     = do n <- newFFCallNo
                                      return  (IAps (ICon fid f {fcallNo = (Just n), iConType = t'}) [] es)
                                   where at' = map iGetType es
                                         t' = foldr1 itFun (at' ++ [rt])
                     listoflists = getLists e
        removeConcat y@(IAps c@(ICon _ (ICSel {})) ts [x@(IAps (ICon fid f@(ICForeign {iConType = t})) [] [e])])
                                 | iGetType e == itFmt && isAVFFWithFmts x =
               do action_list <- mapM mkFF listoflists
                  return (process action_list)
               where (_ , rt)    = itGetArrows (getInnerType t)
                     mkFF es     = do n <- newFFCallNo
                                      return  (IAps c ts [(IAps (ICon fid f {fcallNo = (Just n), iConType = t'}) [] es)])
                                   where at' = map iGetType es
                                         t' = foldr1 itFun (at' ++ [rt])
                     listoflists = getLists e
                     process [_] = y
                     process zs = joinActions zs
        removeConcat w@(IAps x@(ICon fid f@(ICForeign {iConType = t})) ts es)
                                 | isFFWithFmts w =
               do es' <- mapM removeConcat es
                  return (IAps x ts es')
        removeConcat y@(IAps x ts es) =
               do es' <- mapM removeConcat es
                  return (IAps x ts es')
        removeConcat x = return x

        getLists (IAps (ICon _ (ICPrim _ PrimFmtConcat)) _ [e0, e1]) =
               (getLists e0) ++ (getLists e1)
        getLists x = [[x]]

-- #############################################################################
-- #
-- #############################################################################

createValueExprs :: IExpr a -> [IExpr a]
createValueExprs (IAps c _ (e:rest)) | c == icJoinActions = (createValueExprs e ++ concatMap createValueExprs rest)
createValueExprs x | allStrings x                         = [createStringExpr x]
createValueExprs x                                        = [createValueExpr x]

-- #############################################################################
-- #
-- #############################################################################

createValueExpr :: IExpr a -> IExpr a
createValueExpr (IAps (ICon c (ICSel {})) [ITAp b (ITNum s)] [e@(IAps (ICon _ (ICForeign {})) _ _)])
                | c == idAVAction_, b == itBit
                = x
                where x = (IAps (ICon idAVValue_ (ICSel {iConType = tt , selNo = 0, numSel = 2 })) [ITAp itBit $ ITNum s] [e])
                      v0 = head tmpVarIds
                      tt = ITForAll v0 IKStar (ITAp (ITAp (ITCon (idArrow noPosition) (IKFun IKStar (IKFun IKStar IKStar)) TIabstract) (ITAp (ITCon idActionValue_ (IKFun IKStar IKStar) (TIstruct SStruct [idAVValue_,idAVAction_])) (ITVar v0)))
                                                   (ITVar v0) )
createValueExpr (IAps cc@(ICon i (ICPrim _ PrimIf)) ts [cond, e0, e1])
                = x
                where x = (IAps cc [rt] [cond, e0', e1'])
                      e0' = createValueExpr e0
                      e1' = createValueExpr e1
                      rt  = iGetType e0'
createValueExpr x = internalError ("createValueExpr: " ++ ppReadable x)


createActionExpr :: IExpr a -> IExpr a
createActionExpr (IAps (ICon c (ICSel {})) [ITAp b (ITNum s)] [e@(IAps (ICon _ (ICForeign {})) _ _)])
                | c == idAVValue_, b == itBit
                = x
                where x = (IAps (ICon idAVAction_ (ICSel {iConType = tt , selNo = 1, numSel = 2 })) [ITAp itBit $ ITNum s] [e])
                      v0 = head tmpVarIds
                      tt = ITForAll v0 IKStar (ITAp (ITAp (ITCon (idArrow noPosition) (IKFun IKStar (IKFun IKStar IKStar)) TIabstract) (ITAp (ITCon idActionValue_ (IKFun IKStar IKStar) (TIstruct SStruct [idAVValue_,idAVAction_])) (ITVar v0)))
                                                   itAction )
createActionExpr (IAps cc@(ICon i (ICPrim _ PrimIf)) ts [cond, e0, e1])
                = x
                where x = (IAps cc [rt] [cond, e0', e1'])
                      e0' = createActionExpr e0
                      e1' = createActionExpr e1
                      rt  = iGetType e0'
createActionExpr x = joinActions []


allStrings :: IExpr a -> Bool
allStrings (IAps (ICon c (ICSel {})) [ITAp b (ITNum s)] [(IAps (ICon _ (ICForeign {})) _ [e])])
           | c == idAVAction_ && b == itBit && iGetType e == itString
           = True
allStrings (IAps (ICon i (ICPrim _ PrimIf)) _ [_, e0, e1])
           = allStrings e0 && allStrings e1
allStrings _ = False

createStringExpr :: IExpr a -> IExpr a
createStringExpr (IAps (ICon c (ICSel {})) [ITAp b (ITNum s)] [(IAps (ICon _ (ICForeign {})) _ [e])])
                | c == idAVAction_, b == itBit
                = e
createStringExpr (IAps cc@(ICon i (ICPrim _ PrimIf)) ts [cond, e0, e1])
                = x
                where x = (IAps cc [rt] [cond, e0', e1'])
                      e0' = createStringExpr e0
                      e1' = createStringExpr e1
                      rt  = iGetType e0'
createStringExpr x = internalError ("createStringExpr: " ++ ppReadable x)


createRefsAndDefsAndActions :: IExpr a -> ([IExpr a], [IDef a], [IExpr a])
createRefsAndDefsAndActions (IAps (ICon c (ICSel {})) _ [(IAps (ICon _ (ICForeign {})) _ es)]) | c == idAVValue_
                 = (es, [], [])
createRefsAndDefsAndActions  e@(ICon _ ICString {}) = ([e], [], [])
createRefsAndDefsAndActions e | iGetType e == itString = ([(iMkString "%0s"), e], [], [])
createRefsAndDefsAndActions e = ([(iMkString "%0s"), (ICon i (ICValue {iConType = t, iValDef = e}))],
                                 [(IDef i t e [])],
                                 removeConditions (createActionExpr e))
                where i = enumId "_ff" noPosition (fromInteger n)
                      t = iGetType e
                      n = head (getFCallNos e)

getFCallNos :: IExpr a -> [Integer]
getFCallNos (IAps (ICon _ (ICForeign {fcallNo = (Just n)})) _ _) = [n]
getFCallNos (IAps _ _ es) = concatMap getFCallNos es
getFCallNos _ = []

removeConditions :: IExpr a -> [IExpr a]
removeConditions (IAps cc@(ICon i (ICPrim _ PrimIf)) ts [cond, e0, e1]) =
                 (removeConditions e0 ++ removeConditions e1)
removeConditions (IAps c _ (e:rest)) | c == icJoinActions = (removeConditions e ++ concatMap removeConditions rest)
removeConditions x = [x]


-- #############################################################################
-- #
-- #############################################################################

reduceFmt :: IExpr a -> F a (IExpr a)
reduceFmt e =
  do  e' <- reduce False True e
      return (remove e')
  where -- if we're only interested in the value part of an ActionValue foreign function
        -- (i.e. $swrite etc) then don't bother with converting the
        -- args from Fmts .... set the value of "rm_args" to True
        reduce False   first expr@(IAps (ICon m _) _ _) | m == idAVValue_ =
             do e' <- reduce True first expr
                return e'
        -- if this is the first time (and a foreign function call) eliminate any type
        -- variables (should this have been done in IExpand?) and recurse down into the arguments
        reduce rm_args True   (IAps (ICon fid f@(ICForeign {iConType = ict})) ts es)
            | (rt == itFmt) || (any (== itFmt) at) =
            do es' <- mapM (reduce rm_args True) es
               f'  <- reduce rm_args True (ICon fid f {iConType = ict'})
               e'  <- reduce rm_args False (IAps f' [] es')
               return e'
            where (_, rt) = itGetArrows (getInnerType ict)
                  at = map iGetType es
                  ict' = itInst ict ts
        -- if this is the first time (and not a foreign function) recurse down into the arguments
        reduce rm_args True  (IAps f ts es) =
            do es' <- mapM (reduce rm_args True) es
               f'  <- reduce rm_args True f
               e' <- reduce rm_args False (IAps f' ts es')
               return e'
        -- if this is a foreign function call and we're removing args
        -- (for the value half of of an AV expression), eliminate the args.
        reduce True    False (IAps (ICon fid f@(ICForeign {iConType = ict})) ts es)
            | any (== itFmt) at =
            return (IAps (ICon fid f {iConType = rt}) [] [])
            where (at, rt) = itGetArrows (getInnerType ict)
        -- move "if" conditions outside of AVAction_ calls (so the type of the if is action)
        reduce False   False x@(IAps ica@(ICon m _) ts
                                [(IAps ici@(ICon _ (ICPrim _ PrimIf)) [rt] [cond, e0, e1])])
                             | m == idAVAction_ =
            do e0' <- reduce False False (IAps ica ts [e0])
               e1' <- reduce False False (IAps ica ts [e1])
               return (IAps ici [itAction] [cond, e0', e1'])
        -- eliminate Fmt ifs when one half is a don't care
        -- we are treating Fmt like Integer or String rather than Bit#(n)
        reduce rm_args False (IAps (ICon _ (ICPrim _ PrimIf)) _ [cond, e0, (ICon _ (ICUndet it _ _))]) | it == itFmt = return e0
        reduce rm_args False (IAps (ICon _ (ICPrim _ PrimIf)) _ [cond, (ICon _ (ICUndet it _ _)), e1]) | it == itFmt = return e1
        -- move "if" expressions outside of Fmt concat operations
        reduce rm_args False x@(IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc
                      [(IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e0, e1]), e2]) =
            do e0' <- reduce rm_args False (IAps cc tc [e0,e2])
               e1' <- reduce rm_args False (IAps cc tc [e1,e2])
               e'  <- reduce rm_args False (IAps ci ti [cond, e0', e1'])
               return e'
        reduce rm_args False x@(IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc
                      [e2, (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e0, e1])]) =
            do e0' <- reduce rm_args False (IAps cc tc [e2,e0])
               e1' <- reduce rm_args False (IAps cc tc [e2,e1])
               e'  <- reduce rm_args False (IAps ci ti [cond, e0', e1'])
               return e'
        -- reduce a concat of two fmt calls to a single fmt call
        reduce rm_args False x@(IAps (ICon _ (ICPrim _ PrimFmtConcat)) _
                      [(IAps (ICon fid fic@(ICForeign {iConType = t0})) [] es0),
                       (IAps (ICon _       (ICForeign {iConType = t1})) [] es1)]) =
            do let (at0, dt) = itGetArrows t0
                   (at1, _ ) = itGetArrows t1
                   t = foldr1 itFun (at0 ++ at1 ++ [dt])
               return (IAps (ICon fid fic {iConType = t}) [] (es0 ++ es1))
        -- move "if" expressions (of type Fmt) outside of foreign function calls
        reduce rm_args False (IAps (ICon fid f@(ICForeign {iConType = t})) []
                      ((IAps ici@(ICon _ (ICPrim _ PrimIf)) [it] [cond, e0, e1]):rest)) | it == itFmt =
            do n0    <- newFFCallNo
               n1    <- newFFCallNo
               n2    <- newFFCallNo
               e0'   <- reduce rm_args False (IAps (ICon fid f {fcallNo = (Just n0)}) [] [e0])
               e1'   <- reduce rm_args False (IAps (ICon fid f {fcallNo = (Just n1)}) [] [e1])
               rest' <- reduce rm_args False (IAps (ICon fid f {fcallNo = (Just n2)}) [] rest)
               e0''  <- addArg e0' rest'
               e1''  <- addArg e1' rest'
               e0''' <- reduce rm_args False e0''
               e1''' <- reduce rm_args False e1''
               return (IAps ici [rt] [cond, e0''', e1'''])
            where (_  , rt) = itGetArrows t
        reduce rm_args False (IAps icf@(ICon fid f@(ICForeign {})) [] (first:rest))
            | any isIfFmt rest =
            do n  <- newFFCallNo
               e' <- reduce rm_args False (IAps (ICon fid f {fcallNo = (Just n)}) [] rest)
               e'' <- addArg (IAps icf [] [first]) e'
               return e''
        reduce _ _ x = return x

        -- finally turn args of type fmt into "real" $display args
        remove (IAps (ICon fid (ICForeign {iConType = t})) [] [])
                | rt == itAction = joinActions []
               where (_ , rt) = itGetArrows t
        remove (IAps (ICon fid f@(ICForeign {iConType = t})) [] es)
                | any (== itFmt) at = expr
               where (at , rt) = itGetArrows t
                     es' = map remove es
                     es'' = concatMap eliminateFormat es'
                     at' = map iGetType es''
                     t' = foldr1 itFun (at' ++ [rt])
                     expr = remove (IAps (ICon fid f {iConType = t'}) [] es'')
        remove (IAps x ts es) = (IAps x ts (map remove es))
        remove x = x

addArg :: IExpr a -> IExpr a -> F a (IExpr a)
addArg (IAps ici@(ICon _ (ICPrim t PrimIf)) ts [cond, e0, e1]) rest =
    do e0' <- addArg e0 rest
       e1' <- addArg e1 rest
       return (IAps ici ts [cond, e0', e1'])

addArg (IAps icf@(ICon _ (ICForeign {})) [] [first]) rest =
    do e' <- addArg2 first rest
       return e'
    where addArg2 first (IAps ici@(ICon _ (ICPrim t PrimIf)) ts [cond, e0, e1]) =
              do e0' <- addArg2 first e0
                 e1' <- addArg2 first e1
                 return (IAps ici ts [cond, e0', e1'])
          addArg2 first (IAps (ICon fid f@(ICForeign {})) [] es) =
              do n <- newFFCallNo
                 return (IAps (ICon fid f {fcallNo = (Just n)}) [] (first:es))
          addArg2 _ e' = internalError("addArg2: unexpected expr: " ++ ppReadable e')
addArg e _ = internalError ("addArg: " ++ ppReadable e)

isIfFmt :: IExpr a -> Bool
isIfFmt (IAps (ICon _ (ICPrim _ PrimIf)) [it] _) | it == itFmt = True
isIfFmt _ = False

eliminateFormat :: IExpr a -> [IExpr a]
eliminateFormat (IAps (ICon _ ICForeign {iConType = t}) [] es) | rt == itFmt = es
    where (_, rt) = itGetArrows t
-- also remove $format with no arguments
-- XXX perhaps the caller shouldn't have created this expression?
eliminateFormat (ICon _ ICForeign {iConType = t}) | rt == itFmt = []
    where (_, rt) = itGetArrows t
-- and remove don't-care value
-- XXX again, should this be fixed earlier than here?
-- XXX should we warn or error about a don't-care Fmt?
eliminateFormat (ICon _ ICUndet {iConType = t}) | t == itFmt = []
eliminateFormat x = [x]


isActionFFWithFmts :: IExpr a -> Bool
isActionFFWithFmts (IAps (ICon _ (ICForeign {iConType = t})) _ _) =
   (isitAction rt) &&  (any (== itFmt) at)
   where (at , rt) = itGetArrows (getInnerType t)
isActionFFWithFmts _                                          = False

isAVFFWithFmts :: IExpr a -> Bool
isAVFFWithFmts (IAps (ICon _ (ICForeign {iConType = t})) _ _) =
   (isitActionValue_ rt) &&  (any (== itFmt) at)
   where (at , rt) = itGetArrows (getInnerType t)
isAVFFWithFmts _                                              = False

isFFWithFmts :: IExpr a -> Bool
isFFWithFmts e = isActionFFWithFmts e || isAVFFWithFmts e

ssplitFmt_ifc :: [IEFace a] -> F a [IEFace a]
ssplitFmt_ifc ifc_list
    = do let updateIfc (IEFace i xs (Just (e,t)) rules wp fi) = do e' <- ssplitFmt e
                                                                   return (IEFace i xs (Just (e',t)) rules wp fi)
             updateIfc (IEFace i xs _ rules wp fi)            = return (internalError("ssplitFmt_ifc: expression not found"))
         ifc_list' <- mapM updateIfc ifc_list
         return ifc_list'

getInnerType :: IType -> IType
getInnerType (ITForAll id ik t) = (getInnerType t)
getInnerType t = t

-- #############################################################################
-- # Code to inline then eliminate Fmts from ISyntax
-- #############################################################################

iInlineFmts :: IModule a -> IModule a
iInlineFmts imod =
    let tst _ = True
        imod'  = iInlineFmtsPhase1 imod
        imod'' = iInlineFmtsT tst imod'
    in imod''

iInlineFmtsPhase1 :: IModule a -> IModule a
iInlineFmtsPhase1 imod =
    let tst (IAps (ICon _ (ICPrim _ PrimFmtConcat)) _ _) = True
        tst (IAps (ICon _ (ICForeign {})) _ _) = True
        tst e = False
        imod' = (iInlineFmtsT tst imod)
        (imod'', change) = (modPromoteSome imod')
    in if (change) then iInlineFmtsPhase1 imod'' else imod''

iInlineFmtsT :: ((IExpr a) -> Bool) -> IModule a -> IModule a
iInlineFmtsT tst imod@(IModule { imod_local_defs = ds,
                                 imod_rules      = rs,
                                 imod_interface  = ifc}) =
    let smap = M.fromList [ (i, iSubstWhen tst smap dmap e) | IDef i t e _ <- ds, (t == itFmt) ] -- inline any def of type Fmt
        ds' = iDefsMap (iSubstWhen tst smap dmap) ds
        dmap = M.fromList [ (i, e) | IDef i t e _ <- ds' ]
        ifc' = map (iSubstIfc smap dmap) ifc
        rs' = irulesMap (iSubstWhen tst smap dmap) rs
        state_vars' = [ (name, sv { isv_iargs = es' })
                      | (name, sv@(IStateVar { isv_iargs = es }))
                            <- imod_state_insts imod,
                        let es' = map (iSubstWhen tst smap dmap) es ]
        ds'' = [ IDef id t e p | IDef id t e p <- ds', (t /= itFmt || (not (tst e))) ] -- remove any def of type Fmt

    in imod { imod_local_defs  = ds'',
              imod_rules       = rs',
              imod_interface   = ifc',
              imod_state_insts = state_vars' }


-- #############################################################################
-- #
-- #############################################################################



modPromoteSome :: IModule a -> (IModule a, Bool)
modPromoteSome imod@(IModule { imod_local_defs = ds,
                               imod_rules      = rs,
                               imod_interface  = ifc}) =
    let getFirst (a, b)   = a
        getSecond (a, b)  = b
        pDef (IDef id t e p) = ((IDef id t e' p), change)
            where (e', change) = promoteSome e
        pairs = map pDef ds
        ds'  = map getFirst pairs
        change [] = False
        change ps = (foldr1 (||) (map getSecond ps))
        ifc' = ifc
        rs'  = rs
        state_vars' = imod_state_insts imod
    in (imod { imod_local_defs  = ds',
               imod_rules       = rs',
               imod_interface   = ifc',
               imod_state_insts = state_vars' },
        (change pairs))

promoteSome :: IExpr a -> (IExpr a, Bool)
promoteSome e |  t /= itFmt = (e, False)
              where t = iGetType e

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e00, e01]),
                                                            (IAps    (ICon _ (ICPrim _ PrimFmtConcat)) _  [e10, e11])])
              | (pMatch e00 e10) = ((IAps cc tc [e00, (IAps ci ti [cond, e01, e11])]), True)

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e00, e01]),
                                                            (IAps    (ICon _ (ICPrim _ PrimFmtConcat)) _  [e10, e11])])
              | (pMatch e01 e11) = ((IAps cc tc [(IAps ci ti [cond, e00, e10]), e01]), True)

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e00, e01]),
                                                           e10])
             | (pMatch e00 e10) = promoteSome (IAps ci ti [cond, (IAps cc tc [e00, e01     ]),
                                                             (IAps cc tc [e10, emptyFmt])])

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e00, e01]),
                                                           e10])
             | (pMatch e01 e10) = promoteSome (IAps ci ti [cond, (IAps cc tc [e00,      e01]),
                                                             (IAps cc tc [emptyFmt, e10])])

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e00,
                                                            (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e10, e11])])
             | (pMatch e00 e10) = promoteSome (IAps ci ti [cond, (IAps cc tc [e00, emptyFmt]),
                                                             (IAps cc tc [e10, e11     ])])

promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e00,
                                                            (IAps cc@(ICon _ (ICPrim _ PrimFmtConcat)) tc [e10, e11])])
             | (pMatch e00 e11) = promoteSome (IAps ci ti [cond, (IAps cc tc [emptyFmt, e00]),
                                                             (IAps cc tc [e10,      e11])])


promoteSome (IAps ci@(ICon _ (ICPrim _ PrimIf)) ti [cond, e0, e1])
             | (pMatch e0 e1) = (e0, True)

promoteSome (IAps x ts es) =
              let pairs = map promoteSome es
                  getFirst  (a, b) = a
                  getSecond (a, b) = b
                  es' = map getFirst pairs
                  change [] = False
                  change ps = (foldr1 (||) (map getSecond ps))
              in ((IAps x ts es'), (change pairs))
promoteSome x = (x, False)

pMatch :: IExpr a -> IExpr a -> Bool
pMatch e0 e1 = e0 == e1
-- pMatch (IAps (ICon fid0 (ICForeign {iConType = t0})) [] [e0]) (IAps (ICon fid1 (ICFor  eign {iConType = t1})) [] [e1])
--        | fid0 == fid1 && pMatch e0 e1 = True
-- pMatch e0 e1 = e0 == e1
