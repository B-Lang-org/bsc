{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams, PatternGuards, ScopedTypeVariables #-}
module ITransform(

                 -- the transform stage
                 iTransform

                 -- optimize an expression of type Bool
                 , iTransBoolExpr

                 -- optimize an expression of any type
                 , iTransExpr

                 ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Control.Monad(foldM, forM)
import Control.Monad.State(State, runState, gets, get, put)
import Data.List((\\))
import qualified Data.Map as M

import IntegerUtil(mask, integerAnd)
import Util(log2, itos, appFstM, snd3, makePairs, flattenPairs,
            fromJustOrErr)
import PPrint
import IntLit
import Position(noPosition, getPosition)
import Error(internalError, ErrMsg(..), ErrorHandle, bsErrorUnsafe)
import Flags(Flags, optBool)
import FStringCompat(mkFString)
import Id
import Prim
import Pragma(DefProp, defPropsHasNoCSE)
import ISyntax
import ISyntaxUtil
import IPrims(doPrimOp)
import IInline(iSortDs, iInline)
import BExpr

-- For boolean opt
import Intervals
import BoolExp
import BoolOpt

-- import Util(trace_answer)
-- import Debug.Trace(trace, TraceM)
-- import Util(traces)

-----------------------------------------------------------------------------

-- use the special-purpose boolean optimizer to optimize a boolean expression
-- instead of the general-purpose iTransExpr
-- will use BDDs for boolean optimization when -opt-bool is set (like optIRule)
iTransBoolExpr :: Flags -> IExpr a -> IExpr a
iTransBoolExpr flags = optBoolExpr (optBool flags)

-----------------------------------------------------------------------------

iTransExpr :: ErrorHandle -> IExpr a -> (IExpr a, Bool)
iTransExpr errh =
    let ?errh = errh
    in iTransExpr'

iTransExpr' :: (?errh :: ErrorHandle) =>
               IExpr a -> (IExpr a, Bool)
iTransExpr' (IAps f ts es) = iTrAp emptyCtx f ts es
iTransExpr' e = (e, False)

{- not really useful external uses only have one-level transformations exposed
iTransExprLoop :: IExpr a -> IExpr a
iTransExprLoop e =
  let (e', b') = iTransExpr e in
  if b' then -- recurse (try transforming more)
    iTransExprLoop e'
  else e'
-}
-----------------------------------------------------------------------------

iTransform :: ErrorHandle -> Flags -> String -> IModule a -> IModule a
iTransform errh flags prefix =
          iInline False .                -- XXX only for debug
        iTransform1 1 errh flags prefix . iSortDs

iTransform1 :: Integer -> ErrorHandle -> Flags -> String ->
               IModule a -> IModule a
iTransform1 no errh flags prefix imod@(IModule { imod_state_insts = itvs,
                                                 imod_local_defs  = ds,
                                                 imod_rules       = rs,
                                                 imod_interface   = ifc }) =
    imod { imod_state_insts = itvs',
           imod_local_defs  = ds',
           imod_rules       = rs',
           imod_interface   = ifc' }
  where ((itvs', rs', ifc'), ds') = runT errh flags no prefix trMod
        trMod = do
            mapM_ iTrDef ds
            iTransFixupDefNames flags
            rs' <- iTrRules rs
            ifc' <- mapM iTrIfc ifc
            -- clock and reset expressions (in nc and nr) are just wires - do not simplify
            itvs' <- mapM (\ (i, sv@(IStateVar { isv_iargs = es })) ->
                             do es' <- mapM (iTrExprL emptyCtx []) es
                                return (i, sv { isv_iargs = es' }))
                          itvs
            return (itvs', rs', ifc')

iTrIfc :: IEFace a -> T (IEFace a) a
iTrIfc (IEFace i its met mrs wp fi)
    = do met' <- forM met (appFstM  $ iTrExprL emptyCtx [])
         mrs' <- forM mrs iTrRules
         return (IEFace i its met' mrs' wp fi)

iTrDef :: IDef a -> T () a
iTrDef def@(IDef i t e p) = do
          -- traceM ("iTrDef start " ++ ppReadable def)
        e' <- iTrExprL emptyCtx [] e
        -- traceM ("iTrDef process " ++ ppReadable (i, e', expVal e'))
        addDefT i t e' p

iTrRule :: IRule a -> T (IRule a) a
iTrRule r = do
        doBO <- getDoBO
        let ctx = emptyCtx
        -- traceM("iTrRule start " ++ ppReadable (irule_name r))
        c' <- iTrExprL ctx [] (irule_pred r)
        let c'' = optBoolExpr doBO c'
        -- traceM("iTrRule cond " ++ ppReadable (irule_name r, c''))
        e' <- iTrExprL (addT c'' ctx) [] (irule_body r)
        -- traceM("iTrRule body " ++ ppReadable (irule_name r, e'))
        return $ r { irule_pred = c'', irule_body = e' }

iTrRules :: IRules a -> T (IRules a) a
iTrRules (IRules sps rs) = do
        rs' <- mapM iTrRule rs
        return (IRules sps rs')

iTrExprL :: Ctx a -> [(IExpr a, Integer)] -> IExpr a -> T (IExpr a) a
iTrExprL ctx idxs e = expandHRef e >>= iTrExpr ctx idxs

iTrExpr :: Ctx a -> [(IExpr a, Integer)] -> IExpr a -> T (IExpr a) a
iTrExpr ctx idxs (IAps pif@(ICon _ (ICPrim _ PrimIf)) [t] [cnd, thn, els]) = do
        doBO <- getDoBO
        cnd1 <- iTrExpr ctx [] (expValShallow cnd)
        let cnd' = optBoolExpr doBO cnd1
        thn' <- iTrExpr (addT cnd' ctx) idxs thn
        els' <- iTrExpr (addF cnd' ctx) idxs els
--        traceM ("IF " ++ ppString (IAps pif [t] [cnd', thn', els']) ++ "\n   " ++ ppReadable (cnd, cnd0, cnd1))
        iTrExpr' ctx idxs pif [t] [cnd', thn', els']
iTrExpr ctx idxs (IAps pcase@(ICon _ (ICPrim _ PrimCase)) ts@[sz_idx, elem_ty] (idx:dflt:ces)) = do
        idx' <- iTrExpr ctx [] (expValShallow idx)
        let foldFn (res_ces, res_ctx) (c,e) = do
              c' <- iTrExpr ctx [] (expValShallow c)
              let eq_e = iePrimEQ sz_idx idx' c'
              e' <- iTrExpr (addT eq_e res_ctx) idxs e
              return ((c',e'):res_ces, addF eq_e res_ctx)
        (rev_ces', ctx') <- foldM foldFn ([], ctx) (makePairs ces)
        let ces' = flattenPairs (reverse rev_ces')
        dflt' <- iTrExpr ctx' idxs dflt
        iTrExpr' ctx idxs pcase ts (idx':dflt':ces')
iTrExpr ctx idxs (IAps psel@(ICon _ (ICPrim _ PrimArrayDynSelect)) ts@[elem_ty, ITNum sz_idx] [arr, idx]) = do
        idx' <- iTrExpr ctx [] (expValShallow idx)
        arr' <- iTrExpr ctx ((idx,sz_idx):idxs) (expValShallow arr)
        iTrExpr' ctx idxs psel ts [arr', idx']
iTrExpr ctx idxs@((idx,sz_idx):rest_idxs) (IAps pupd@(ICon _ (ICPrim _ PrimArrayDynUpdate)) ts@[elem_ty, ITNum sz_upd_idx] [arr, upd_idx, val]) = do
        upd_idx' <- iTrExpr ctx [] (expValShallow upd_idx)
        let mkExtend in_sz out_sz e =
                let k = out_sz - in_sz
                    ts = [ITNum k, ITNum in_sz, ITNum out_sz]
                in  IAps icPrimZeroExt ts [e]
            eq_e = let (max_sz, e1, e2)
                           | sz_idx > sz_upd_idx = (sz_idx, idx, mkExtend sz_upd_idx sz_idx upd_idx)
                           | sz_idx < sz_upd_idx = (sz_upd_idx, mkExtend sz_idx sz_upd_idx idx, upd_idx)
                           | otherwise           = (sz_upd_idx, idx, upd_idx)
                   in  iePrimEQ (ITNum max_sz) e1 e2
        val' <- iTrExpr (addT eq_e ctx) idxs (expValShallow val)
        arr' <- iTrExpr (addF eq_e ctx) idxs (expValShallow arr)
        iTrExpr' ctx idxs pupd ts [arr', upd_idx', val']
iTrExpr ctx idxs@((idx,sz_idx):rest_idxs) (IAps pbld@(ICon i (ICPrim _ PrimBuildArray)) ts es) = do
        let foldFn (res_es, res_ctx) (n, e) = do
              let n_lit = iMkLitAt (getPosition i) (aitBit (ITNum sz_idx)) n
              let eq_e = iePrimEQ (ITNum sz_idx) idx n_lit
              e' <- iTrExpr (addT eq_e res_ctx) rest_idxs (expValShallow e)
              return (e':res_es, addF eq_e res_ctx)
        (rev_es', _) <- foldM foldFn ([], ctx) (zip [0..] es)
        iTrExpr' ctx idxs pbld ts (reverse rev_es')
iTrExpr ctx idxs (IAps pand@(ICon _ (ICPrim _ PrimBAnd)) ts [e1, e2]) = do
        e1' <- iTrExpr ctx [] e1
        e2'' <- iTrExpr (addT e1'  ctx) [] (expValShallow e2)
        e1'' <- iTrExpr (addT e2'' ctx) [] (expValShallow e1')
        iTrExpr' ctx idxs pand ts [e1'', e2'']
iTrExpr ctx idxs (IAps por@(ICon _ (ICPrim _ PrimBOr)) ts [e1, e2]) = do
        e1' <- iTrExpr ctx [] e1
        e2'' <- iTrExpr (addF e1'  ctx) [] (expValShallow e2)
        e1'' <- iTrExpr (addF e2'' ctx) [] (expValShallow e1')
        iTrExpr' ctx idxs por ts [e1'', e2'']
iTrExpr ctx idxs (IAps f ts es) = do
        es' <- mapM (iTrExpr ctx []) es
        iTrExpr' ctx idxs f ts es'
-- XXX This makes some conditions simpler, but maybe other things get worse?
iTrExpr ctx idxs (ICon _ (ICUndet t _ _)) | t == itAction = return icNoActions
iTrExpr ctx idxs (ICon i (ICUndet t k (Just e))) = do
  e' <- iTrExpr ctx idxs e
  return (ICon i (ICUndet t k (Just e')))
iTrExpr ctx idxs e = return e

expandHRef :: IExpr a -> T (IExpr a) a
expandHRef (IAps f ts es) = do
        f' <- expandHRef f
        es' <- mapM expandHRef es
        return (IAps f' ts es')
expandHRef e@(ICon i (ICValue { })) = do
        me <- getDefT i
        case me of
            Just e' -> return e'
            Nothing -> return e
-- probably not necessary
-- included so we could re-run ITransform if we wanted
expandHRef (ICon i (ICUndet t k (Just e))) = do
  e' <- expandHRef e
  return (ICon i (ICUndet t k (Just e')))
expandHRef e = return e        -- XXX
--expandHRef e = internalError ("expandHRef " ++ ppReadable e)

iTrExpr' :: Ctx a -> [(IExpr a, Integer)] -> IExpr a -> [IType] -> [IExpr a] -> T (IExpr a) a
iTrExpr' ctx idxs f ts es = do
        errh <- gets errHandle
        let (et, trans) = let ?errh = errh
                          in iTrAp ctx f ts es
        if trans then
            iTrExpr ctx idxs et
        else
            do
                e <- runCSE et
                let t = iGetType e
                    isBool = t == itBit1
                if isBool && isT ctx e then
                    return iTrue
                else if isBool && isF ctx e then
                    return iFalse
                else
                    return e

runCSE :: IExpr a -> T (IExpr a) a
runCSE e@(IAps _ _ _) = do
  -- This used to recurse on the arguments, but we don't need to do that,
  -- because "runCSE" is called from iTrExpr, which already recurses on the
  -- arguments, so runCSE will already have been called on the arguments.
  let t = iGetType e
  -- Only CSE applications that are not actions or tuple method values
  if not (isActionType t || isPairType t) then
      newExprT t e
   else
      return e
-- should CSE values boxed by undefined
-- they have something to CSE against
runCSE (ICon i (ICUndet t k (Just v))) = do
  v' <- runCSE v
  let e' = ICon i (ICUndet t k (Just v'))
  return e'
runCSE e = return e

-- recursively transform an expression
-- noting that a nontrivial transformation has happened
{-# INLINE iTrAp2 #-}
iTrAp2 :: (?errh :: ErrorHandle) =>
          Ctx a -> IExpr a -> [IType] -> [IExpr a] -> (IExpr a, Bool)
iTrAp2 ctx e ts es = (iTrApExp ctx e ts es, True)

-- transform an expression, forgetting whether an transformation
-- was done or not - used for recursive transformation
{-# INLINE iTrApExp #-}
iTrApExp :: (?errh :: ErrorHandle) =>
            Ctx a -> IExpr a -> [IType] -> [IExpr a] -> IExpr a
iTrApExp ctx e ts es = fst (iTrAp ctx e ts es)

-- transform an expression, if it is an application
iTrExprIfAp :: (?errh :: ErrorHandle) =>
               Ctx a -> IExpr a -> (IExpr a, Bool)
iTrExprIfAp ctx (IAps f ts es) = iTrAp ctx f ts es
iTrExprIfAp _   e              = (e,False)

--
-- Transform an application.
-- The arguments need to be unfolded when they are matched against IAps nodes,
-- since these are already CSEed.
-- Returns a flag indicating whether the expression changed or not
iTrAp :: (?errh :: ErrorHandle) =>
         Ctx a -> IExpr a -> [IType] -> [IExpr a] -> (IExpr a, Bool)

-- eliminate null actions
iTrAp ctx (ICon _ (ICPrim _ PrimJoinActions)) _ [ICon _ (ICPrim _ PrimNoActions), e] = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimJoinActions)) _ [e, ICon _ (ICPrim _ PrimNoActions)] = (e, True)

-- if True  t e         -->  t
-- if False t e         -->  e
-- if c t t             -->  t
-- if c True False      -->  c
-- if c True  e         -->  c || e
-- if c False True      -->  not c
-- if c False e         -->  not c && e
-- if c t True          -->  not c || t
-- if c t False         -->  c && t
-- if c t _             -->  t
-- if c _ e             -->  e
iTrAp ctx p@(ICon _ (ICPrim _ PrimIf)) [t] [cnd, thn, els]
        | isT ctx cnd = (thn, True)
        | isF ctx cnd = (els, True)
        | eqE thn els = (thn, True)
        | otherwise   = case (t == itBit1, thn, els) of
           (True, ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }), ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })) -> (cnd, True)
           (True, ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }), _                            ) -> iTrAp2 ctx iOr  [] [cnd, els]
           (True, ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }), ICon _ (ICInt { iVal = IntLit { ilValue = 1 } })) -> iTrAp2 ctx iNot [] [cnd]
           (True, ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }), _                            ) -> iTrAp2 ctx iAnd [] [iTrApExp ctx iNot [] [cnd], els]
           (True, _,                             ICon _ (ICInt { iVal = IntLit { ilValue = 1 } })) -> iTrAp2 ctx iOr  [] [iTrApExp ctx iNot [] [cnd], thn]
           (True, _,                             ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })) -> iTrAp2 ctx iAnd [] [cnd, thn]
           (_,    _,                             _                            ) ->
                case (expVal cnd, expVal thn, expVal els) of

                -- if c1 t (if c2 t e)  -->  if (c1 || c2) t e
                (_, _, IAps (ICon _ (ICPrim _ PrimIf)) _ [cnd2, thn2, els2]) | eqE thn thn2
                        -> iTrAp2 ctx p [t] [ieOr cnd cnd2, thn, els2]
{-
-- This opt is an improvement, but it triggers too much inlining in some
-- examples.  I'm reverting it, for backwards compatibility, until we add a
-- pass (after ITransform? during VeriQuirks?) that lifts subexpressions
-- from defs whose expression is too large.
                -- if c1 (if c2 t e) e  -->  if (c1 && c2) t e
                (_, IAps (ICon _ (ICPrim _ PrimIf)) _ [cnd2, thn2, els2], _) | eqE els els2
                        -> iTrAp2 ctx p [t] [ieAnd cnd cnd2, thn2, els]
-}

                -- XXX Can this ever be harmful?  It removes a constant...
                -- if (x == k) k e  -->  if (x == k) x e
                (IAps (ICon _ (ICPrim _ PrimEQ)) _ [x, k@(ICon _ _)], _, _)
                  |  k == thn && thn /= x
                  -> iTrAp2 ctx p [t] [cnd, x, els]

                -- We used to perform this tagging
                -- (only for bit-type, not Action, and not in the evaluator)
                --   if c e _  -->  if c e _[e]
                -- But this could use an ActionValue value outside its scope.
                -- Also, it appears to be unnecessary (and prematurely picks
                -- a value.  So it has been removed.  But the opt also
                -- included two other opts, which we preserve (and apply even
                -- in the evaluator:

                --   if c _ _  -->  _
                -- XXX This only applies if one of the don't-care has not
                -- XXX been tagged.  Can we ignore tags?  Is this opt even used?
                (_, ICon _ (ICUndet { imVal = Nothing }), ICon _ (ICUndet {}))
                    -> (els, True)
                (_, ICon _ (ICUndet {}), ICon _ (ICUndet { imVal = Nothing }))
                    -> (thn, True)

{-
-- This opt was OK when we still had the above optimization for tagging of
-- don't-care values.  When we remove it, this opt becomes a problem
-- (somes modules hang in the transform stage).  Until we understand why,
-- I'm removing it.
                --   if c {e1, e2} _  -->  if c {e1, e2} {_, _}
                (_, ICon i (ICUndet { iuKind = u, imVal = Nothing }),
                    IAps c@(ICon _ (ICPrim _ PrimConcat)) ts@[ITNum n, ITNum k, ITNum l] [e1, e2])
                    -> let t1 = itBitN n
                           t2 = itBitN k
                           thn' = IAps c ts [ICon i (ICUndet t1 u Nothing), ICon i (ICUndet t2 u Nothing)]
                       in  iTrAp2 ctx p [t] [cnd, thn', els]
                (_, IAps c@(ICon _ (ICPrim _ PrimConcat)) ts@[ITNum n, ITNum k, ITNum l] [e1, e2],
                    ICon i (ICUndet { iuKind = u, imVal = Nothing }))
                    -> let t1 = itBitN n
                           t2 = itBitN k
                           els' = IAps c ts [ICon i (ICUndet t1 u Nothing), ICon i (ICUndet t2 u Nothing)]
                       in  iTrAp2 ctx p [t] [cnd, thn, els']
-}

                -- Special case for turning pack.unpack into an identity
                -- if (select _ l _ e == c) (c              ++ select k m _ e) x  -->  IF k+m == l
                -- if (select _ l _ e == c) (select _ l _ e ++ select k m _ e) x
                (IAps (ICon _ (ICPrim _ PrimEQ))      _ [sel1, c],
                 IAps (ICon _ (ICPrim _ PrimConcat)) ts [c', sel2],
                 _) | eqE c c' &&
                      (case expVal sel1 of
                        IAps (ICon _ (ICPrim _ PrimSelect)) [_, ITNum ls, _] [e] ->
                              case expVal sel2 of
                                IAps (ICon _ (ICPrim _ PrimSelect)) [ITNum k, ITNum m, _] [e'] -> k + m == ls && eqE e e'
                                ICon _ (ICUndet { imVal = Nothing }) -> True
                                _ -> False
                        _ -> False
                      )
                        -> iTrAp2 ctx p [t] [cnd, IAps icPrimConcat ts [sel1, sel2], els]

                -- if c (x1++x2) (x1++y2)  -->  x1 ++ (if c x2 y2)
                -- if c (x1++x2) (y1++x2)  -->  (if c x1 y1) ++ x2
                -- check if we make progress to avoid infinite loops
                (_,
                 IAps pc@(ICon _ (ICPrim _ PrimConcat)) ts@[t1,t2,_]   [x1, x2],
                 IAps    (ICon _ (ICPrim _ PrimConcat)) ts'            [y1, y2]
                 ) | ts == ts',
                     let (e1', opt1) = iTrAp ctx p [aitBit t1] [cnd, x1, y1],
                     let (e2', opt2) = iTrAp ctx p [aitBit t2] [cnd, x2, y2],
                     opt1 || opt2 ->
                     iTrAp2 ctx pc ts [e1', e2']
                -- if (not c) t e -->  if c e t
                (IAps (ICon _ (ICPrim _ PrimBNot)) _ [c], _, _)
                        -> iTrAp2 ctx p [t] [c,els,thn]

                -- if c t e --> if c t[c=True] e[c=False]
                -- ie. substitute known value of c in sub-exprs XXX:
                -- This doesn't handle the general case of
                -- substituting the condition in the sub-exprs, it
                -- only handles replacing the input expr when it is c
                -- or !c.  There is a worry that general substitution
                -- could create extra logic in the presence of sharing
                -- and be computationally expensive due to repeated
                -- traversal of expressions doing different
                -- substitutions.
                (_,_,_) | eqE cnd thn -> iTrAp2 ctx p [t] [cnd,iTrue,els]
                (_,_,_) | eqE cnd els -> iTrAp2 ctx p [t] [cnd,thn,iFalse]
                (_,IAps (ICon _ (ICPrim _ PrimBNot)) _ [x],_) | eqE cnd x
                                      -> iTrAp2 ctx p [t] [cnd,iFalse,els]
                (_,_,IAps (ICon _ (ICPrim _ PrimBNot)) _ [x]) | eqE cnd x
                                      -> iTrAp2 ctx p [t] [cnd,thn,iTrue]

                _ -> (IAps p [t] [cnd, thn, els], False)

-- Boolean optimization

-- False && e  --> False
-- e && False  --> False
-- e1 && e2    --> e1                IF e1 IMPLIES e2
-- e2 && e1    --> e2                IF e2 IMPLIES e1
-- these two cases may be logically redundant, but the
-- compiler might be able to optimize one path and not the other
-- e1 && e2    --> False        IF e1 IMPLIES ~e2
-- e2 && e1    --> False        IF e2 IMPLIES ~e1
iTrAp ctx p@(ICon _ (ICPrim _ PrimBAnd)) _ [c1, c2]
         | isF ctx c1 || isF ctx c2 = (iFalse, True) -- fast special case
         | isUndet c1 || isUndet c2 = (iFalse, True)
         | implies ctx c1 c2        = (c1, True)
         | implies ctx c2 c1        = (c2, True)
         | impliesnot ctx c1 c2     = (iFalse, True)
         | impliesnot ctx c2 c1     = (iFalse, True)
         | otherwise                = (IAps p [] [c1, c2], False)

-- True || e  --> True
-- e || True  --> True
-- e1 || e2   --> e1                IF e2 IMPLIES e1
-- e2 || e1   --> e2                IF e1 IMPLIES e2
-- these two cases may be logically redundant, but the
-- compiler might be able to optimize one path and not the other
-- e1 || e2   --> True                 IF ~e1 IMPLIES e2
-- e1 || e2   --> True          IF ~e2 IMPLIES e1

iTrAp ctx p@(ICon _ (ICPrim _ PrimBOr)) _ [c1, c2]
         | isT ctx c1 || isT ctx c2 = (iTrue, True) -- fast special case
         | isUndet c1 || isUndet c2 = (iTrue, True)
         | implies ctx c2 c1        = (c1, True)
         | implies ctx c1 c2        = (c2, True)
         | notimplies ctx c1 c2     = (iTrue, True)
         | notimplies ctx c2 c1     = (iTrue, True)
         | otherwise                = (IAps p [] [c1, c2], False)

-- not True           -->  False
-- not False          -->  True
-- not (not e)        -->  e
-- not (e1 && e2)     -->  not e1 || not e2
-- not (e1 || e2)     -->  not e1 && not e2
-- not (e1 RELOP e2)  -->  e1 (inv RELOP) e2
-- not (if c t e)     -->  if c (not t) (not e)
-- XXX There is no rule for pushing inside dynamic array select/update
iTrAp ctx p@(ICon _ (ICPrim _ PrimBNot)) _ [c]
         | isF ctx c = (iTrue, True)
         | isT ctx c = (iFalse, True)
         | otherwise = case expVal c of
              IAps   (ICon _ (ICPrim _ PrimBNot)) _  [e]        -> (e, True)
              IAps   (ICon _ (ICPrim _ PrimBAnd)) _  [e1, e2]   -> iTrAp2 ctx iOr  [] [iTrApExp ctx iNot [] [e1], iTrApExp ctx iNot [] [e2]]
              IAps   (ICon _ (ICPrim _ PrimBOr))  _  [e1, e2]   -> iTrAp2 ctx iAnd [] [iTrApExp ctx iNot [] [e1], iTrApExp ctx iNot [] [e2]]
              IAps i@(ICon _ (ICPrim _ PrimIf))  [t] [e1,e2,e3] -> iTrAp2 ctx i [t] [e1, iTrApExp ctx iNot [] [e2], iTrApExp ctx iNot [] [e3]]
              u@(ICon i (ICUndet t k Nothing)) -> (u, True)
              _                                                 -> (IAps p [] [c], False)

-- e == e --> True
iTrAp ctx (ICon _ (ICPrim _ PrimEQ)) _ [e, e'] | e == e' = (iTrue, True)

-- e <= e --> True
-- e < e --> False
iTrAp ctx (ICon _ (ICPrim _ p)) _ [e, e'] | isLE p, e == e' = (iTrue, True)
  where isLE = (`elem` [PrimULE, PrimSLE])
iTrAp ctx (ICon _ (ICPrim _ p)) _ [e, e'] | isLT p, e == e' = (iFalse, True)
  where isLT = (`elem` [PrimULT, PrimSLT])

-- XXX: preserve the _ "kind"? Or treat different _ differently?
-- _ == e --> _
-- Note that this transformation is wrong for values of size 0. All values of size 0 (even undetermined or undefined ones) are 0.
iTrAp ctx (ICon _ (ICPrim _ PrimEQ)) [ITNum n] [e1@(ICon _ (ICUndet {iuKind = u, imVal = Nothing})), e2] | n > 0 = (icUndet itBit1 u, True)
-- e == _ --> _
iTrAp ctx (ICon _ (ICPrim _ PrimEQ)) [ITNum n] [e1, e2@(ICon _ (ICUndet {iuKind = u, imVal = Nothing}))] | n > 0 = (icUndet itBit1 u, True)


-- e + c1 == c2  -->  e == c2 - c1
-- e - c1 == c2  -->  e == c2 + c1
--   This code does not treat other relational operators, because
--   the flipped versions are not equivalent in the presence of over-
--   and under-flow.
-- e ^ c1 == c2  -->  e == c2 ^ c1
iTrAp ctx rel_c@(ICon _ (ICPrim _ PrimEQ)) t1@[ITNum i1] [e', c2] |  -- app of a PrimEQ with a single type variable
    (isIConInt c2) &&  -- c2 is a constant
    case expVal e' of
        (IAps (ICon _ (ICPrim _ op)) t2@[ITNum i2] [e, c1]) ->       -- app of a prim op with a single type variable
             (isIConInt c1) && (not (isIConInt e)) &&  -- c1 is a constant, e is not a constant (to ensure progress)
             ((op == PrimAdd) || (op == PrimSub) || (op == PrimXor)) &&   -- op is one of these
             (i1 == i2)  -- the type variables are the same
        _ -> False
  = case expVal e' of
        (IAps opc@(ICon _ (ICPrim _ op)) _ [e, c1]) ->
            let
                inv_op = case op of
                             PrimAdd -> PrimSub
                             PrimSub -> PrimAdd
                             PrimXor -> PrimXor
                             _ -> internalError
                                  ("ITransform.iTrAp.inv_op: " ++ ppString op)

                -- c3 == iTrap ctx inv_op t2 [c2,c1]
                -- do the computation here:
                c3 = case (doPrimOp (getIExprPosition opc) inv_op t1 [c2,c1]) of
                       Just (Right e) -> e
                       x -> internalError ("iTrAp: doPrimOp: " ++ ppReadable x)
            in
                -- any reason to use "icPrimEQ" etc instead of reusing "rel_c"?
                iTrAp2 ctx rel_c t1 [e, c3]
        _ -> internalError "ITransform.iTrAp(PrimEQ).expVal e': bad form"


-- For these next two, we only want to perform the optimization when we know
-- that it leads to an improvement in the expression, otherwise we risk
-- preventing case statement reconstruction by obscuring the comparison.

-- e1 ++ e2 == e3 => (e1 == e3[0:i1 - 1] && e2 == e3[i1:i3])
iTrAp ctx eq@(ICon ideq (ICPrim _ PrimEQ)) t_eq@[ITNum i_eq]
         [e_concat@(IAps cat_con@(ICon _ (ICPrim _ PrimConcat))
                         cat_ty@[ITNum i1, ITNum i2, ITNum i3]
                         cat_args@[e1, e2]),
          e3] | i3 == i_eq = -- otherwise the comparison is buggy
      -- try to improve e1_eq and e2_eq
      let improved x = (x == iTrue) || (x == iFalse)
      in if ((improved e1_eq) || (improved e2_eq))
         then iTrAp2 ctx iAnd [] [e1_eq, e2_eq]
         else -- no benefit from splitting, so just use the optimized sub-exprs
              (IAps eq t_eq [cat, e3'],  (mod_cat || mod_e3))
  where e1_eq = iTrApExp ctx icPrimEQ [ITNum i1] [e1,e3_e1]
        e2_eq = iTrApExp ctx icPrimEQ [ITNum i2] [e2,e3_e2]
        e3_e1 = iTrApExp ctx (icSelect (getIdPosition ideq)) [ITNum i1, ITNum i2, ITNum i3] [e3]
        e3_e2 = iTrApExp ctx (icSelect (getIdPosition ideq)) [ITNum i2, ITNum 0,  ITNum i3] [e3]
        (cat,mod_cat) = iTrAp ctx cat_con cat_ty cat_args
        (e3',mod_e3)  = iTrExprIfAp ctx e3

-- e3 == e1 ++ e2 => (e1 == e3[0:i1 - 1] && e2 == e3[i1:i3])
iTrAp ctx eq@(ICon ideq (ICPrim _ PrimEQ)) t_eq@[ITNum i_eq]
         [e3,
          e_concat@(IAps cat_con@(ICon _ (ICPrim _ PrimConcat))
                         cat_ty@[ITNum i1, ITNum i2, ITNum i3]
                         cat_args@[e1, e2])] | i3 == i_eq = -- otherwise the comparison is buggy
      let improved x = (x == iTrue) || (x == iFalse)
      in if ((improved e1_eq) || (improved e2_eq))
         then iTrAp2 ctx iAnd [] [e1_eq, e2_eq]
         else -- no benefit from splitting, so just use the optimized sub-exprs
              (IAps eq t_eq [e3', cat], (mod_cat || mod_e3))
  where e1_eq = iTrApExp ctx icPrimEQ [ITNum i1] [e1,e3_e1]
        e2_eq = iTrApExp ctx icPrimEQ [ITNum i2] [e2,e3_e2]
        e3_e1 = iTrApExp ctx (icSelect (getIdPosition ideq)) [ITNum i1, ITNum i2, ITNum i3] [e3]
        e3_e2 = iTrApExp ctx (icSelect (getIdPosition ideq)) [ITNum i2, ITNum 0,  ITNum i3] [e3]
        (cat,mod_cat) = iTrAp ctx cat_con cat_ty cat_args
        (e3',mod_e3)  = iTrExprIfAp ctx e3

-- select n 0 n e  -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimSelect)) [n, ITNum 0, n'] [e] | n == n' = (e, True)

-- select 0 _ _ e  -->  0
iTrAp ctx (ICon _ (ICPrim _ PrimSelect)) [t@(ITNum 0), _, _] [_]  = (mkZero t, True)

-- e * 0  -->  0
-- 0 * e  -->  0
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [_,_,sz] [e,c] | isZero c = (mkZero sz, True)
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [_,_,sz] [c,e] | isZero c = (mkZero sz, True)

-- e * 1  -->  e
-- 1 * e  -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [se,sk@(ITNum k_size),sz] [e,c] | isOne c = (e', True)
    where e' = iTrApExp ctx icPrimConcat [sk,se,sz] [iMkLitSize k_size 0, e]
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [sk@(ITNum k_size),se,sz] [c,e] | isOne c = (e', True)
    where e' = iTrApExp ctx icPrimConcat [sk,se,sz] [iMkLitSize k_size 0, e]

-- e * 2^k  -->  e << k
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [se,sk@(ITNum k_size),sz] [e, ICon _ (ICInt { iVal = IntLit { ilValue = n } })]
  | m /= Nothing = iTrAp2 ctx icPrimSL [sz, ITNum 32] [e', iMkLit itNat k]
    where e' = iTrApExp ctx icPrimConcat [sk, se, sz] [iMkLitSize k_size 0, e]
          m  = iLog2 n
          k  = fromJustOrErr "iTraAp iLog2" m
-- 2^k * e  -->  e << k
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [sk@(ITNum k_size),se,sz] [ICon _ (ICInt { iVal = IntLit { ilValue = n } }), e]
  | m /= Nothing = iTrAp2 ctx icPrimSL [sz, ITNum 32] [e', iMkLit itNat k]
    where e' = iTrApExp ctx icPrimConcat [sk, se, sz] [iMkLitSize k_size 0, e]
          m  = iLog2 n
          k  = fromJustOrErr "iTraAp iLog2" m

-- 0 | e  -->  e
-- 1 | e  -->  1
-- 0 & e  -->  0
-- 1 & e  -->  e
-- and v.v. (with better granularity)
iTrAp ctx p@(ICon _ (ICPrim _ PrimOr)) [ITNum n] [ICon _ (ICInt {iVal = IntLit {ilValue = i}}), e] | n > 0 =
   case getMaskTail i n of
     Zeroes l ->
      let k = n - l
          -- XXX expression duplication
          hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
          tl = iTrApExp ctx sel [ITNum l, ITNum 0, ITNum n] [e]
      in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
     Ones l   ->
      let k = n - l
          hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
          tl = iMkLitSize l (2^l - 1) -- all ones
      in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
 where sel = icSelect (getIExprPosition p)

iTrAp ctx p@(ICon _ (ICPrim _ PrimOr)) t@[ITNum n] [e, c@(ICon _ (ICInt {}))] = iTrAp ctx p t [c, e]

iTrAp ctx p@(ICon _ (ICPrim _ PrimAnd)) [ITNum n] [ICon _ (ICInt {iVal = IntLit {ilValue = i}}), e] | n > 0 =
  case getMaskTail i n of
    Zeroes l ->
     let k = n - l
         hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
         tl = iMkLitSize l 0 -- all zeroes
     in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
    Ones l   ->
     let k = n - l
         -- XXX expression duplication
         hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
         tl = iTrApExp ctx sel [ITNum l, ITNum 0, ITNum n] [e]
     in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
 where sel = icSelect (getIExprPosition p)

iTrAp ctx p@(ICon _ (ICPrim _ PrimAnd)) t@[ITNum n] [e, c@(ICon _ (ICInt {}))] = iTrAp ctx p t [c, e]

-- 0 ^ e --> e
-- 1 ^ e --> ~e
-- and v.v.
-- with better granularity
iTrAp ctx p@(ICon _ (ICPrim _ PrimXor)) [ITNum n] [ICon _ (ICInt {iVal = IntLit {ilValue = i}}), e] | n > 0 =
  case getMaskTail i n of
    Zeroes l ->
     let k = n - l
         -- XXX expression duplication
         hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
         tl = iTrApExp ctx sel [ITNum l, ITNum 0, ITNum n] [e]
     in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
    Ones l   ->
     let k = n - l
         -- XXX expression duplication
         hd = iTrApExp ctx p [ITNum k] [iMkLitSize k (i `div` 2^l), IAps sel [ITNum k, ITNum l, ITNum n] [e]]
         tl = iTrApExp ctx icPrimInv [ITNum l] [IAps sel [ITNum l, ITNum 0, ITNum n] [e]]
     in iTrAp2 ctx icPrimConcat [ITNum k, ITNum l, ITNum n] [hd, tl]
 where sel = icSelect (getIExprPosition p)

iTrAp ctx p@(ICon _ (ICPrim _ PrimXor)) t@[ITNum n] [e, c@(ICon _ (ICInt {}))] = iTrAp ctx p t [c, e]

{-
iTrAp ctx (ICon _ (ICPrim _ PrimOr))  _ [c, e] | isZero    c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimOr))  _ [e, c] | isZero    c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimOr))  _ [c, e] | isAllOnes c = (c, True)
iTrAp ctx (ICon _ (ICPrim _ PrimOr))  _ [e, c] | isAllOnes c = (c, True)

iTrAp ctx (ICon _ (ICPrim _ PrimAnd)) _ [c, e] | isZero    c = (c, True)
iTrAp ctx (ICon _ (ICPrim _ PrimAnd)) _ [e, c] | isZero    c = (c, True)
iTrAp ctx (ICon _ (ICPrim _ PrimAnd)) _ [c, e] | isAllOnes c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimAnd)) _ [e, c] | isAllOnes c = (e, True)



-- 0 ^ e  -->  e
-- e ^ 0  -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimXor)) _ [c, e] | isZero c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimXor)) _ [e, c] | isZero c = (e, True)

-- 1 ^ e  -->  ~e
-- e ^ 1  -->  ~e
iTrAp ctx (ICon _ (ICPrim _ PrimXor)) [t] [c, e] | isAllOnes c = iTrAp2 ctx icPrimInv [t] [e]
iTrAp ctx (ICon _ (ICPrim _ PrimXor)) [t] [e, c] | isAllOnes c = iTrAp2 ctx icPrimInv [t] [e]
-}

-- 0 + e  -->  e
-- e + 0  -->  e
-- e - 0  -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimAdd)) _ [c, e] | isZero c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimAdd)) _ [e, c] | isZero c = (e, True)
iTrAp ctx (ICon _ (ICPrim _ PrimSub)) _ [e, c] | isZero c = (e, True)

-- e - e  -->  0
iTrAp ctx (ICon _ (ICPrim _ PrimSub)) [t] [e, e'] | e == e' = (mkZero t, True)

-- e / 1    -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimQuot)) _ [e, c] | isOne c = (e, True)

-- e / 2^k  -->  e >> k
iTrAp ctx (ICon _ (ICPrim _ PrimQuot)) [se,_] [e, ICon _ (ICInt { iVal = IntLit { ilValue = n } })]
  | m /= Nothing = iTrAp2 ctx icPrimSRL [se] [e, iMkLit itNat k]
    where m = iLog2 n
          k = fromJustOrErr "iTraAp iLog2" m

-- e % 1    --> 0
iTrAp ctx (ICon _ (ICPrim _ PrimRem)) [_,sk] [_,c] | isOne c = (mkZero sk, True)

-- e % 2^k  --> e[k-1:0]  (with optional zero extension)
iTrAp ctx (ICon remid (ICPrim _ PrimRem)) [se,sk@(ITNum k_size)] [e, ICon _ (ICInt { iVal = IntLit { ilValue = n } })]
  | m /= Nothing = if (pad == 0)
                   then (e', True)
                   else iTrAp2 ctx icPrimConcat [ITNum pad, ITNum k, sk] [iMkLitSize pad 0, e']
    where e'  = iTrApExp ctx (icSelect (getIdPosition remid)) [(ITNum k), ITNum 0, se] [e]
          m   = iLog2 n
          k   = fromJustOrErr "iTraAp iLog2" m
          pad = k_size - k

-- e   <    0  -->  False
-- e   <=   0  -->  e == 0
-- e   <    1  -->  e == 0
-- e   <= 0xe  -->  e /= 0xf
-- e   <  0xf  -->  e /= 0xf
-- e   <= 0xf  -->  True
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [_] [_, c] | isZero    c = (iFalse, True)
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [t] [e, c] | isZero    c = iTrAp2 ctx icPrimEQ [t] [e, c]
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [t] [e, c] | isOne     c = iTrAp2 ctx icPrimEQ [t] [e, mkZero t]
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [t] [e, c] | isAlmost  c = iTrAp2 ctx iNot     []  [iTrApExp ctx icPrimEQ [t] [e, inc c]]
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [t] [e, c] | isAllOnes c = iTrAp2 ctx iNot     []  [iTrApExp ctx icPrimEQ [t] [e, c]]
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [_] [_, c] | isAllOnes c = (iTrue, True)

-- 0xf <    e  -->  False
-- 0xf <=   e  -->  e == 0xf
-- 0xe <    e  -->  e == 0xf
-- 1   <=   e  -->  e /= 0
-- 0   <    e  -->  e /= 0
-- 0   <=   e  -->  True
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [_] [c, _] | isAllOnes c = (iFalse, True)
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [t] [c, e] | isAllOnes c = iTrAp2 ctx icPrimEQ [t] [e, c]
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [t] [c, e] | isAlmost  c = iTrAp2 ctx icPrimEQ [t] [e, inc c]
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [t] [c, e] | isOne     c = iTrAp2 ctx iNot     []  [iTrApExp ctx icPrimEQ [t] [e, mkZero t]]
iTrAp ctx (ICon _ (ICPrim _ PrimULT)) [t] [c, e] | isZero    c = iTrAp2 ctx iNot     []  [iTrApExp ctx icPrimEQ [t] [e, c]]
iTrAp ctx (ICon _ (ICPrim _ PrimULE)) [_] [c, _] | isZero    c = (iTrue, True)

-- e < 0 (signed)   ==> sign-bit
-- e <= -1 (signed) ==> sign-bit
iTrAp ctx (ICon i (ICPrim _ PrimSLT)) [ITNum n] [e, c] | isZero c = iTrAp2 ctx sel [ITNum 1, ITNum (n - 1), ITNum n] [e]
  where sel = icSelect (getIdPosition i)
iTrAp ctx (ICon i (ICPrim _ PrimSLE)) [ITNum n] [e, c] | isAllOnes c = iTrAp2 ctx sel [ITNum 1, ITNum (n - 1), ITNum n] [e]
  where sel = icSelect (getIdPosition i)

-- Bit fields of size 0 always have the value 0.  Proceed accordingly.
iTrAp ctx (ICon _ (ICPrim _ p)) [ITNum 0] _ | argRes p = (iMkLitSize 0 0, True)
  where argRes p = p `elem` [PrimAdd, PrimSub, PrimAnd, PrimOr, PrimXor, PrimInv, PrimNeg]
-- shifts take two type arguments (the item size and the index size)
iTrAp ctx (ICon _ (ICPrim _ p)) [ITNum 0,_] _ | p `elem` [PrimSL, PrimSRL, PrimSRA] = (iMkLitSize 0 0, True)
iTrAp ctx (ICon _ (ICPrim _ PrimMul)) [_,_,ITNum 0] _ = (iMkLitSize 0 0, True) -- PrimMul takes three numeric type arguments
iTrAp ctx (ICon _ (ICPrim _ p)) [ITNum 0] _ | eqOp p = (iTrue, True)
  where eqOp p = p `elem` [PrimEQ, PrimULE, PrimSLE]
iTrAp ctx (ICon _ (ICPrim _ p)) [ITNum 0] _ | ltOp p = (iFalse, True)
  where ltOp p = p `elem` [PrimULT, PrimSLT]
iTrAp ctx (ICon _ (ICPrim _ PrimSignExt)) [_, ITNum 0, ITNum s] _ = (iMkLitSize s 0, True)

-- --e --> e
-- ~~e --> e
-- - (if c t e)  -->  if c (-t) (-e)
-- ~ (if c t e)  -->  if c (~t) (~e)
-- ~ (a ++ b) -> (~a) ++ (~b)
-- - _ -> _
-- ~ _ -> _
iTrAp ctx cneg@(ICon _ (ICPrim _ p)) [ty] [exp] | p == PrimNeg || p == PrimInv =
    case expVal exp of
    IAps cneg2@(ICon _ (ICPrim _ p')) [ty] [e] | p' == p -> (e, True)
    IAps cif@(ICon _ (ICPrim _ PrimIf)) [tif] [c, t, e] | isIConInt t || isIConInt e ->
        iTrAp2 ctx cif [tif] [c, iTrApExp ctx cneg [ty] [t], iTrApExp ctx cneg [ty] [e]]
    IAps ccat@(ICon _ (ICPrim _ PrimConcat)) ts@[l, m, _] [e1, e2] | p == PrimInv ->
        iTrAp2 ctx ccat ts [iTrApExp ctx cneg [l] [e1], iTrApExp ctx cneg [m] [e2]]
    u@(ICon i (ICUndet t k Nothing)) -> (u, True)
    _ -> iTrApTail ctx cneg [ty] [exp]

-- e >> n  -->  0 ++ select (k-n) n k e
iTrAp ctx (ICon srl (ICPrim _ PrimSRL)) [t@(ITNum k), _] [e, ICon _ (ICInt { iVal = IntLit { ilValue = n } })] =
        let z = iMkLitSize n 0
            tt = mkNumConT (k-n)
            tn = mkNumConT n
            e' = iTrApExp ctx (icSelect (getIdPosition srl)) [tt, tn, t] [e]
        in  if n >= k then
                (mkZero t, True)
            else
                iTrAp2 ctx icPrimConcat [tn, tt, t] [z, e']

-- e << n  -->  trunc (e ++ 0)
iTrAp ctx (ICon sl (ICPrim _ PrimSL)) [t@(ITNum k), _] [e, ICon _ (ICInt { iVal = IntLit { ilValue = n } })] =
        let z = iMkLitSize n 0
            tt = mkNumConT (k-n)
            tn = mkNumConT n
            e' = iTrApExp ctx (icSelect (getIdPosition sl)) [tt, mkNumConT 0, t] [e]
        in  if n >= k then
                (mkZero t, True)
            else
                iTrAp2 ctx icPrimConcat [tt, tn, t] [e', z]

-- e :: Bit 1 >> x or e :: Bit 1 << x -> if (x == 0) e else 0 --> (x == 0) && e
iTrAp ctx (ICon _ (ICPrim _ p)) [ITNum 1, ITNum t] [e, shft] | p `elem` [PrimSL, PrimSRL] =
    iTrAp2 ctx icIf [itBit1] [isZero, e, mkZero (ITNum 1)]
  where isZero = IAps icPrimEQ [ITNum t] [shft, mkZero (ITNum t)]


-- e :: Bit 1 >> x (arithmetic) --> e
-- we rely on looping to recursively simplify e
iTrAp ctx (ICon _ (ICPrim _ PrimSRA)) [ITNum 1, ITNum t] [e, shft] = (e, True)

-- Associativity and commutativity (for +, &, |)
-- (k1 op (k2 op e))  -->   (e op (k1 op k2))
-- (k1 op (e op k2))  -->   (e op (k1 op k2))
-- ((e op k1) op k2)  -->   (e op (k1 op k2))
-- ((k1 op e) op k2)  -->   (e op (k1 op k2))
iTrAp ctx p@(ICon _ (ICPrim _ prim)) [t] [e1,e2]
  | prim `elem` [PrimAdd, PrimAnd, PrimOr] &&
    (((isIConInt e1) && (isConstExprForPrim prim e2)) ||
     ((isIConInt e2) && (isConstExprForPrim prim e1)))
    = iTrAp2 ctx p [t] [e,k]
      where e  = if (isIConInt e1) then (nonConstPart e2) else (nonConstPart e1)
            k1 = if (isIConInt e1) then e1 else (constPart e1)
            k2 = if (isIConInt e1) then (constPart e2) else e2
            k  = case (doPrimOp (getIExprPosition p) prim [t] [k1,k2]) of
                   Just (Right res) -> res
                   _ -> internalError("iTrAp: associativity")

-- extract n k e h l -->  zeroExt (h-l+1) (k-(h-l+1)) k (select (h-l+1) l n e)
iTrAp ctx fun@(ICon iext (ICPrim _ PrimExtract)) ts@[tn@(ITNum n), _, ITNum k] es@[e, eh, el]
  | (ICon _ (ICInt { iVal = IntLit { ilValue = h } })) <- eh
  , (ICon _ (ICInt { iVal = IntLit { ilValue = l } })) <- el
  = let
        exp = iTrApExp ctx (icSelect (getIdPosition iext)) [mkNumConT sz, mkNumConT l, tn] [e]
        sz = mask 32 (h-l+1) -- mask it to allow h == l-1
        k_sz = if k < sz
               then internalError("extraction size (" ++ show sz ++ ") " ++
                                  "is larger than the expected result (" ++
                                  show k ++ "):\n" ++
                                  ppReadable (IAps fun ts es))
                else k - sz
    in
--        iTrAp ctx icPrimZeroExt [mkNumConT k_sz, mkNumConT sz, mkNumConT k] [exp]
        iTrAp2 ctx icPrimConcat [mkNumConT k_sz, mkNumConT sz, mkNumConT k] [iMkLitSize k_sz 0, exp]

-- select n k m e --> error, n+k > m
iTrAp ctx fun@(ICon sel (ICPrim _ PrimSelect)) ts@[ITNum n, ITNum k, ITNum m] as | n+k > m =
    bsErrorUnsafe ?errh
        [(getIdPosition sel,
          EBitSel (show n) (show k) (show m) (ppString (IAps fun ts as)))]

-- select n ? ? _  -->  _
iTrAp ctx (ICon sel (ICPrim _ PrimSelect)) [ITNum n, _, _] [ICon _ (ICUndet { iuKind = u, imVal = Nothing })] = (icUndet (itBitN n) u, True)

{-
-- XXX join with above
conApN _ ctx fun@(ICon isel (ICPrim _ PrimSelect)) args@[T (ITNum k), T (ITNum m), T (ITNum n)]
        | k > n-m || n-m < 0
        = compileError ("conApN select: bad bit selection\n" ++
                             ppReadable (getIdPosition isel) ++ ppReadable (mkAp fun args))
-}

{-
-- XXX what's this?
iTrAp ctx fun@(ICon iext (ICPrim _ PrimExtract)) args@[T tn, T tk, E e, E eh, E el]
        | eh == el && isNumConT tk && getNumConT tk == 1
        = iTrAp ctx icSelect [T (mkNumConT 1), T (mkNumConT 0), T tn, E exp]
  where exp = IAps icPrimSRL [tn] [e, el]
-}

-- x::Bit1 == 1  -->  x
-- x::Bit1 == 0  -->  not x
iTrAp ctx e0@(ICon _ (ICPrim _ PrimEQ)) [ITNum 1] [e, ICon _ (ICInt { iVal = IntLit { ilValue = i } })]
        | i == 0    = iTrAp2 ctx iNot [] [e]
        | i == 1    = (e, True)
        | otherwise = internalError ("conApN ==")

-- (if b1 then c1 else if b2 then c2 else ... cn) == c -->
-- if b1 then (c1 == c) else if b2 then (c2 == c) ... (cn == c)
-- (other direction is handled by the flip rule below)
-- also can be applied to any op which has a 1-bit result
-- (and possibly are heuristics for when it's worth applying to other ops)
iTrAp ctx rel_c@(ICon _ (ICPrim _ p)) t1@[ITNum i1] [e', c] |
    -- app of a 1-bit prim with a single type variable
    (isIConInt c) &&  -- c is a constant
    -- XXX can we include other ops?
    (p `elem` [PrimEQ, PrimULT, PrimULE, PrimSLT, PrimSLE]) &&
    (isIfElseOfIConInt e')
  = let ap (IAps i@(ICon _ (ICPrim _ PrimIf)) ts [cnd, thn, els]) =
            -- the result of the "if" is now 1-bit
            (IAps i [itBit1] [cnd, ap thn, ap els])
        ap (ICon _ (ICValue { iValDef = e })) = ap e
        ap e = iTrApExp ctx rel_c t1 [e, c]
    in  (ap e', True)

-- c RELOP x  -->  x (flip RELOP) c
iTrAp ctx e0@(ICon _ (ICPrim _ p)) [t] [e1, e2]
  | (Just fp) <- flipOp p
  , isIConInt e1 && not (isIConInt e2)
  = fp [t] [e2, e1]
  where flipOp PrimEQ  = Just $ \ ts es -> iTrAp2 ctx icPrimEQ ts es
        flipOp PrimULT = Just $ \ ts es -> iTrAp2 ctx iNot [] [iTrApExp ctx icPrimULE ts es]
        flipOp PrimULE = Just $ \ ts es -> iTrAp2 ctx iNot [] [iTrApExp ctx icPrimULT ts es]
        flipOp PrimSLT = Just $ \ ts es -> iTrAp2 ctx iNot [] [iTrApExp ctx icPrimSLE ts es]
        flipOp PrimSLE = Just $ \ ts es -> iTrAp2 ctx iNot [] [iTrApExp ctx icPrimSLT ts es]
        flipOp _ = Nothing

iTrAp ctx p@(ICon _ (ICPrim _ PrimConcat)) ts@[s1@(ITNum i1), s2@(ITNum i2), s3@(ITNum i3)] as@[e1, e2] =
    case map expValConcat as of
    -- ignore 0 sized args
    _ | i1 == 0 -> (e2, True)
    _ | i2 == 0 -> (e1, True)
    -- _ ++ _  --> _
    [ICon _ (ICUndet { imVal = Nothing }), ICon _ (ICUndet { iuKind = u, imVal = Nothing })]
        -> (icUndet (aitBit s3) u, True)
    -- c1 ++ (c2 ++ e)  -->  (c1++c2) ++ e
    [ICon _ (ICInt { iVal = IntLit { ilValue = c1 } }),
     IAps (ICon _ (ICPrim _ PrimConcat)) [ITNum isc2, se, _] [ICon _ (ICInt { iVal = IntLit { ilValue = c2 } }), e]]
        -> iTrAp2 ctx p [mkNumConT isc1c2, se, s3] [iMkLitSize isc1c2 (c1 * 2^isc2 + c2), e]
          where isc1c2 = i1 + isc2

    -- select ? ? ? e1 ++ (select ? ? ? e1 ++ e2)  -->  (select ? ? ? e1 ++ select ? ? ? e1) ++ e2
    -- enables next transform
    [x1@(IAps ps@(ICon _ (ICPrim _ PrimSelect)) _ [e1]),                -- size l
        (IAps pc@(ICon _ (ICPrim _ PrimConcat))
                [s2s@(ITNum s2i), e2s, _]
                [x2@(IAps (ICon _ (ICPrim _ PrimSelect)) _ [e1']),
                 e2])]
        | e1 == e1'
        -> iTrAp2 ctx pc [s12s, e2s, s3] [ss, e2]
        where ss = iTrApExp ctx pc [s1,s2s,s12s] [x1, x2]
              s12s = mkNumConT (i1 + s2i)

    -- select l (m+k) n e ++ select k m n e  -->  select (l+k) m n e
    [IAps p@(ICon _ (ICPrim _ PrimSelect)) [ITNum il', ITNum imk, n] [e],
     IAps   (ICon _ (ICPrim _ PrimSelect)) [ITNum ik', m@(ITNum im), n'] [e']]
        |  i1 == il' && i2 == ik' && n == n' && eqE e e'
        && i3 == i1 + i2 && imk == im + i2
        -> iTrAp2 ctx p [s3, m, n] [e]
    -- (e1 ++ select l (m+k) n e2) ++ select k m n e2 -> (e1 ++ select (l+k) m n e)
    [x1@(IAps pc@(ICon _ (ICPrim _ PrimConcat))
                [e1s@(ITNum e1i), sel1s@(ITNum sel1i), _]
                [e1, sel1@(IAps (ICon _ (ICPrim _ PrimSelect))
                                [ITNum il', ITNum imk, n] [e2])]),
     sel2@(IAps ps@(ICon _ (ICPrim _ PrimSelect))
                  [ITNum ik', m@(ITNum im), n'] [e2'])]
        | sel1i == il' && i2 == ik' && n == n' && eqE e2 e2'
        && i3 == i1 + i2 && imk == im + i2
        -> iTrAp2 ctx pc [e1s, s12s, s3] [e1, ss]
        where ss = iTrApExp ctx pc [sel1s,s2,s12s] [sel1, sel2]
              s12s = mkNumConT (sel1i + i2)

    -- _ ++ select k m n e  -->       select (l+k) m n e                IF n-m >= l+k
    -- _ ++ select k m n e  -->  _ ++ select (n-m) m n e                IF n-m <  l+k
    [ICon _ (ICUndet { iuKind = u, imVal = Nothing }),
     IAps ps@(ICon _ (ICPrim _ PrimSelect)) [ITNum ik', m@(ITNum im), n@(ITNum inn)] [e]]
        |  i2 == ik' && d /= i1
        -> --trace ("_ ++ sel\n" ++ ppReadable (mkAp p as)) $
           if d <= 0 then
               iTrAp2 ctx ps [s3, m, n] [e]
           else
               iTrAp2 ctx p [mkNumConT d, tnm, s3]
                            [icUndet (itBitN d) u, iTrApExp ctx ps [tnm, m, n] [e]]
          where nm = inn - im
                d = i3 - nm
                tnm = mkNumConT nm

    -- select k m n e ++ _  -->  select (l+k) (m-l) n e                        IF m >= l
    -- select k m n e ++ _  -->  select (m+k) 0     n e ++ _
    [IAps ps@(ICon _ (ICPrim _ PrimSelect)) [ITNum ik', m@(ITNum im), n@(ITNum inn)] [e],
     ICon _ (ICUndet { iuKind = u, imVal = Nothing })]
        |  i1 == ik' && (im >= i2 || d /= i2)
        -> --trace ("sel ++ _\n" ++ ppReadable (mkAp p as, im, i2)) $
           if im >= i2 then
               iTrAp2 ctx ps [s3, mkNumConT (im-i2), n] [e]
           else
               iTrAp2 ctx p [tmk, mkNumConT d, s3]
                            [iTrApExp ctx ps [tmk, ITNum 0, n] [e], icUndet (itBitN d) u]
          where tmk = mkNumConT (im+i1)
                d = i3 - (im+i1)
    -- (if c t0 e0) ++ (if c t1 e1) --> if c (t0 ++ t1) (e0 ++ e1)
    [IAps pif@(ICon _ (ICPrim _ PrimIf)) _ [cnd0, t0, e0],
     IAps     (ICon _ (ICPrim _ PrimIf)) _ [cnd1, t1, e1]] | cnd0 == cnd1 ->
        iTrAp2 ctx pif [itBitN i3] [cnd0, t', e']
      where t' = iTrApExp ctx p ts [t0, t1]
            e' = iTrApExp ctx p ts [e0, e1]

    -- (if c thn _) ++ e --> thn ++ e
    [IAps (ICon _ (ICPrim _ PrimIf)) _ [_, thn, els], e]
      | isUndet thn && noRefs els -> iTrAp2 ctx p ts [els, e]
      | isUndet els && noRefs thn -> iTrAp2 ctx p ts [thn, e]

    -- e ++ (if c thn _) --> e ++ thn
    [e, IAps (ICon _ (ICPrim _ PrimIf)) _ [_, thn, els]]
      | isUndet thn && noRefs els -> iTrAp2 ctx p ts [e, els]
      | isUndet els && noRefs thn -> iTrAp2 ctx p ts [e, thn]

    _ -> iTrApTail ctx p ts as

iTrAp ctx ps@(ICon _ (ICPrim _ PrimSelect)) ts@[k@(ITNum ik), m@(ITNum im), n] [e] =
    case expVal e of
    -- select k m n (select n p q e)  -->  select k (m+p) q e
    IAps (ICon _ (ICPrim _ PrimSelect)) [n', ITNum ip, q] [e]
        | n == n'
        -> iTrAp2 ctx ps [k, mkNumConT (im+ip), q] [e]

    -- select k 0 n (e1 ++ e2)  -->  select (k-l2) 0 l1 e1 ++ e2        IF k >= l2
    IAps pc@(ICon _ (ICPrim _ PrimConcat)) [l1, l2@(ITNum il2), n'] [e1, e2]
        | n == n' && im == 0 && ik >= il2
        -> iTrAp2 ctx pc [mkNumConT j, l2, k] [sel, e2]
          where j = ik - il2
                sel = iTrApExp ctx ps [mkNumConT j, m, l1] [e1]

    -- select k m n (e1 ++ e2)  -->  select k      m l2 e2                IF k+m <= l2
    --                                -->  select k (m-l2) l1 e1                IF m >= l2
    -- otherwise                -->  select (k + m - l2) 0 l1 e1 ++ select (l2 - m) m l2 e2
    IAps pc@(ICon _ (ICPrim _ PrimConcat)) [l1, l2@(ITNum il2), n'] [e1, e2]
        | n == n'
        -> if im >= il2 then
               iTrAp2 ctx ps [k, mkNumConT (im - il2), l1] [e1]
           else if (ik + im <= il2) then
               iTrAp2 ctx ps [k, m, l2] [e2]
           else iTrAp2 ctx pc [mkNumConT l1', mkNumConT l2', k] [e1', e2']
          where e1' = iTrApExp ctx ps [mkNumConT l1', mkNumConT 0, l1] [e1]
                l1' = ik + im - il2
                e2' = iTrApExp ctx ps [mkNumConT l2', m, l2] [e2]
                l2' = il2 - im
{- Disable this fix for bug 1429 because it causes problems with the
   bug 1490 situation.

    -- select k m n (if c t e)  --> if c (select k m n t) (select k m n e)
    IAps pif@(ICon _ (ICPrim _ PrimIf)) _ [cnd,thn,els]
        -> iTrAp2 ctx pif [itBitN ik] [cnd, thn', els']
      where thn' = iTrApExp ctx ps ts [thn]
            els' = iTrApExp ctx ps ts [els]
-}
    _ -> iTrApTail ctx ps ts [e]

-- (e1 ++ 0) + (e2 ++ e3)  -->  (e1+e2) ++ e3
-- XXX only special case so far
iTrAp ctx op@(ICon _ (ICPrim _ PrimAdd)) ts as =
    case map expVal as of
    [ICon _ (ICInt { iVal = IntLit { ilValue = c } } ),
     IAps co@(ICon _ (ICPrim _ PrimConcat)) [t1, t2@(ITNum it2), t3]  [ICon _ (ICInt { iVal = IntLit { ilValue = c2 } }), e]
     ]        | r == 0
        -> iTrAp2 ctx co [t1, t2, t3] [iMkLit (aitBit t1) (q+c2), e]
        where (q,r) = quotRem c (2^it2)
    [IAps co@(ICon _ (ICPrim _ PrimConcat)) [t1, t2@(ITNum it2), t3]  [e, ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })],
     ICon _ (ICInt { iVal = IntLit { ilValue = c } } )
     ]        | q == 0
        -> iTrAp2 ctx co [t1, t2, t3] [e, iMkLit (aitBit t2) r]
        where (q,r) = quotRem c (2^it2)
    _ -> iTrApTail ctx op ts as

-- (e1 ++ e2) `op` (e3 ++ e4)  -->  (e1 `op` e3) ++ (e2 `op` e4)
-- ((e1 ++ e1') ++ e2) `op` (e3 ++ c)   -->  ((e1 ++ e1') ++ e2) `op` ((e3 ++ c1) ++ c2)
-- this doesn't improve things on its own, but can open up other transformations
iTrAp ctx op@(ICon _ (ICPrim _ p)) [t@(ITNum it)] as
    | p `elem` [PrimAnd, PrimOr, PrimXor] =
    let default_res = iTrApTail ctx op [t] as
        applyOp (sz, eA, eB) = (sz, iTrApExp ctx op [ITNum sz] [eA, eB])
        concatFn (sz, expr) (sz_so_far, expr_so_far) =
            let sz_total = sz_so_far + sz
            in  (sz_total, iTrApExp ctx icPrimConcat
                             [ITNum sz, ITNum sz_so_far, ITNum sz_total]
                             [expr, expr_so_far])
    in  case map expVal as of
          [e1, e2] -> case (findConcatBreaks it e1 e2) of
                        [] -> internalError "iTrAp: findConcatBreaks"
                        [_] -> -- no progress made, so leave as is
                               default_res
                        ps -> let res = snd $ foldr1 concatFn (map applyOp ps)
                              in  -- indicate that a transform occurred
                                  (res, True)
          _ -> -- can this happen?
               default_res

-- signExt n n e  -->  e
iTrAp ctx (ICon _ (ICPrim _ PrimSignExt)) [_, t1, t2] [e] | t1 == t2 = (e, True)

-- constant folding
iTrAp ctx c@(ICon _ (ICPrim _ p)) ts as | canDoOp = (e, True)
  where (canDoOp, e) = case (doPrimOp (getIExprPosition c) p ts as) of
                           Just (Right res) -> (True, res)
                           _ -> (False, internalError("iTrAp: ICPrim"))

iTrAp ctx f ts es = iTrApTail ctx f ts es

-- constant folding
iTrApTail :: Ctx a -> IExpr a -> [IType] -> [IExpr a] -> (IExpr a, Bool)
iTrApTail ctx c@(ICon _ (ICPrim _ p)) ts as | canDoOp = (e, True)
  where (canDoOp, e) = case (doPrimOp (getIExprPosition c) p ts as) of
                           Just (Right res) -> (True, res)
                           _ -> (False, internalError("iTrapTail: ICPrim"))

iTrApTail ctx f ts es = (IAps f ts es, False)

expVal :: IExpr a -> IExpr a
expVal (ICon _ (ICValue { iValDef = e })) = e
expVal e = e

-- Like expVal but expands concats one level deeper, so that
-- the patterns can match things like ((a ++ (select..)) ++ (select..))
expValConcat :: IExpr a -> IExpr a
expValConcat (ICon _ (ICValue { iValDef = e })) = expValConcat e
expValConcat (IAps p@(ICon _ (ICPrim _ PrimConcat)) ts es) = IAps p ts (map expVal es)
expValConcat e = e

-------------------------

findConcatBreaks :: Integer -> IExpr a -> IExpr a ->
                    [(Integer, IExpr a, IExpr a)]
findConcatBreaks sz eA@(IAps (ICon _ (ICPrim _ PrimConcat))
                          [ITNum itA1, ITNum itA2, ITNum itA3] [eA1, eA2]) eB =
    case (splitConstExpr itA1 itA2 eB) of
      Nothing -> [(sz, eA, eB)]
      Just (eB1, eB2) -> findConcatBreaks itA1 eA1 eB1 ++
                         findConcatBreaks itA2 eA2 eB2
findConcatBreaks sz eA eB@(IAps (ICon _ (ICPrim _ PrimConcat))
                             [ITNum itB1, ITNum itB2, ITNum itB3] [eB1, eB2]) =
    case (splitConstExpr itB1 itB2 eA) of
      Nothing -> [(sz, eA, eB)]
      Just (eA1, eA2) -> findConcatBreaks itB1 eA1 eB1 ++
                         findConcatBreaks itB2 eA2 eB2
findConcatBreaks sz eA eB = [(sz, eA, eB)]


splitConstExpr :: Integer -> Integer -> IExpr a  -> Maybe (IExpr a, IExpr a)
splitConstExpr n n2 (ICon _ ic@(ICInt { iVal = IntLit { ilValue = c } })) =
    let c1 = iMkLit (aitBit (mkNumConT n)) (c `div` 2^n2)
        c2 = iMkLit (aitBit (mkNumConT n2)) (mask n2 c)
    in  Just (c1, c2)
splitConstExpr n n2 (ICon _ (ICUndet { iuKind = u, imVal = Nothing })) =
    let u1 = icUndet (aitBit (mkNumConT n)) u
        u2 = icUndet (aitBit (mkNumConT n2)) u
    in  Just (u1, u2)
splitConstExpr n n2 e@(IAps (ICon _ (ICPrim _ PrimConcat))
                            [(ITNum it1), (ITNum it2), (ITNum it3)]
                            [e1, e2]) =
    case (compare n it1) of
      EQ -> Just (e1, e2)
      LT -> let n2' = it1 - n
            in  case (splitConstExpr n n2' e1) of
                  Nothing -> Nothing
                  Just (e1A, e1B) ->
                      let t1' = ITNum n2'        -- (it1 - n)
                          t2' = ITNum it2        -- (n2 + n - it1)
                          t3' = ITNum (it3 - n)  -- n2
                          rest = IAps icPrimConcat [t1', t2', t3'] [e1B, e2]
                      in  Just (e1A, rest)
      GT -> let n' = n - it1
            in  case (splitConstExpr n' n2 e2) of
                  Nothing -> Nothing
                  Just (e2A, e2B) ->
                      let t1' = ITNum it1
                          t2' = ITNum n'  -- (n - it1)
                          t3' = ITNum n   -- (it3 - n2)
                          rest = IAps icPrimConcat [t1', t2', t3'] [e1, e2A]
                      in  Just (rest, e2B)
-- Nothing else is considered a splittable expression
splitConstExpr _ _ _ = Nothing


-----------------------------------------------------------------------------

addT :: IExpr a -> Ctx a -> Ctx a
addT e ctx = --trace ("addT\n" ++ ppReadable (e, ctx, addT' (expValAndOrCmp e) ctx)) $
                addT' (expValAndOrCmp e) ctx
  where addT' e (Ctx vs be) = Ctx (addEqs e vs) (bAdd e be)
        addEqs (IAps (ICon _ (ICPrim _ PrimEQ)) _ [i, ICon _ (ICInt { iVal = IntLit { ilValue = v } })]) vs = M.insert i v vs
        -- XXX case for when the const is on the left?
        -- XXX case for (e1 == e2), when e1 or e2 exists in the set, add the other as the same val
        addEqs (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) vs = addEqs e1 (addEqs e2 vs)
        addEqs (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) vs = addNEqs e vs
        addEqs _ vs = vs
        -- XXX case for != ?
        addNEqs (IAps (ICon _ (ICPrim _ PrimBOr)) _ [e1, e2]) vs = addNEqs e1 (addNEqs e2 vs)
        addNEqs (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) vs = addEqs e vs
        addNEqs _ vs = vs

addF :: IExpr a -> Ctx a -> Ctx a
addF e ctx = addT (ieNot e) ctx

expValAndOrCmp :: IExpr a -> IExpr a
expValAndOrCmp (IAps e ts es) = IAps e ts (map expValAndOrCmp es)
expValAndOrCmp (ICon _ (ICValue { iValDef = e@(IAps (ICon _ (ICPrim _ p)) _ _ )})) | isAndOrCmp p = expValAndOrCmp e
expValAndOrCmp e = e

isAndOrCmp :: PrimOp -> Bool
isAndOrCmp p = p `elem` [PrimBAnd, PrimBOr, PrimBNot, PrimEQ, PrimULT, PrimULE, PrimSLT, PrimSLE]

expValShallow :: IExpr a -> IExpr a
expValShallow (IAps e ts es) = IAps e ts (map expValShallow es)
expValShallow (ICon _ (ICValue { iValDef = e@(IAps (ICon _ (ICPrim _ p)) _ _ )})) | p == PrimBNot = expValShallow e
                                                                                  | isAndOrCmp p = e
expValShallow e = e

{-
expValAndOr :: IExpr a -> IExpr a
expValAndOr (IAps e ts es) = IAps e ts (map expValAndOr es)
expValAndOr (ICon _ (ICValue { iValDef = e@(IAps (ICon _ (ICPrim _ p)) _ _ )})) | isAndOr p = expValAndOr e
  where isAndOr p = p `elem` [PrimBAnd, PrimBOr, PrimBNot]
expValAndOr e = e
-}

isT :: Ctx a -> IExpr a -> Bool
isT ctx@(Ctx vs be) e = --traces ("isT\n" ++ ppReadable (e, expValAndOrCmp e, ctx, isT' (expValAndOrCmp e))) $
                        isT' (expValAndOrCmp e)
  where isT' e =
            bImplies be e ||
            case e of
            IAps (ICon _ (ICPrim _ PrimEQ)) _ [i, ICon _ (ICInt { iVal = IntLit { ilValue = v } })] ->
--                traces ("isT EQ" ++ ppReadable (i, v, M.toList vs)) $
                case M.lookup i vs of
                Just k -> v == k
                Nothing -> False
            IAps (ICon _ (ICPrim _ PrimBNot)) _ [IAps (ICon _ (ICPrim _ PrimEQ)) _ [i, ICon _ (ICInt { iVal = IntLit { ilValue = v } })]] ->
--                traces ("isT NE" ++ ppReadable (i, v, M.toList vs)) $
                case M.lookup i vs of
                Just k -> v /= k
                Nothing -> False
            _ -> False


isF :: Ctx a -> IExpr a -> Bool
isF ctx@(Ctx vs be) e = --traces ("isF\n" ++ ppReadable (e, expValAndOrCmp e, ctx, isF' (expValAndOrCmp e))) $
                        isF' (expValAndOrCmp e)
  where isF' e =
            bImplies be (ieNot e) ||
            case e of
            IAps (ICon _ (ICPrim _ PrimEQ)) _ [i, ICon _ (ICInt { iVal = IntLit { ilValue = v } })] ->
                case M.lookup i vs of
                Just k -> v /= k
                Nothing -> False
            IAps (ICon _ (ICPrim _ PrimBNot)) _ [IAps (ICon _ (ICPrim _ PrimEQ)) _ [i, ICon _ (ICInt { iVal = IntLit { ilValue = v } })]] ->
                case M.lookup i vs of
                Just k -> v == k
                Nothing -> False
            _ -> False

{-
isT :: Ctx a -> IExpr a -> Bool
isT _ (ICon _ (ICInt { iVal = IntLit { ilValue = 1 } })) = True
isT _ _ = False

isF :: Ctx a -> IExpr a -> Bool
isF _ (ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })) = True
isF _ _ = False
-}

-- a --> b
implies :: Ctx a -> IExpr a -> IExpr a -> Bool
implies ctx a b = isT (addT a ctx) b

-- ~a --> b
notimplies :: Ctx a -> IExpr a -> IExpr a -> Bool
notimplies ctx a b = isT (addF a ctx) b

-- a --> ~b
impliesnot :: Ctx a -> IExpr a -> IExpr a -> Bool
impliesnot ctx a b = isF (addT a ctx) b

-----------------------------------------------------------------------------

-- The BExpr is a formula of what we know is true
data Ctx a = Ctx (M.Map (IExpr a) IValue) (BExpr a)
type IValue = Integer

emptyCtx :: Ctx a
emptyCtx = Ctx M.empty bNothing

instance PPrint (Ctx a) where
    pPrint d p (Ctx es be) =
        (text "Ctx " $+$ text "  ")
         <> (pPrint d 0 (M.toList es) $+$
             pPrint d 0 be)

{-
bSetLess :: Ctx a -> Ctx a -> Bool
bSetLess (Ctx sm e) (Ctx sm' e') =
        isOrdSubset (M.toList sm) (M.toList sm') && bImpliesB e' e
-}

-----------------------------------------------------------------------------

data MaskTail = Zeroes Integer | Ones Integer

-- this is fast because the GHC libraries (i.e. GMP) do a good job here
getMaskTail :: Integer -> Integer -> MaskTail
getMaskTail mask size | zeroes_gcd > 1 =
                        let result = log2 zeroes_gcd
                        in if (result > size) then
                             internalError("ITransform.getMaskTail: " ++
                                            ppReadable(mask, size, zeroes_gcd, result))
                           else
                             Zeroes result
                      | ones_gcd > 1   =
                        let result = log2 ones_gcd
                        in if (result > size) then
                             internalError("ITransform.getMaskTail: " ++
                                           ppReadable(mask, size, ones_gcd, result))
                           else Ones result
                      | otherwise = internalError ("ITransform.getMaskTail: " ++
                                                   ppReadable (mask, size))
  where zeroes_gcd = gcd mask power
        ones_gcd   = gcd (mask+1) power
        power      = 2^size

isZero :: IExpr a -> Bool
isZero (ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })) = True
isZero _ = False

isOne :: IExpr a -> Bool
isOne (ICon _ (ICInt { iVal = IntLit { ilValue = 1 } })) = True
isOne _ = False

isAllOnes :: IExpr a -> Bool
isAllOnes (ICon _ (ICInt { iConType = ITAp b (ITNum i), iVal = IntLit { ilValue = n } })) = b == itBit && 2^i == n+1
isAllOnes _ = False

isAlmost :: IExpr a -> Bool
isAlmost (ICon _ (ICInt { iConType = ITAp b (ITNum i), iVal = IntLit { ilValue = n } })) = b == itBit && 2^i == n+2
isAlmost _ = False

iLog2 :: Integer -> Maybe Integer
iLog2 i =
        if i > 0 && (i `integerAnd` (i-1)) == 0 then
             Just (log2 i)
        else
             Nothing

inc :: IExpr a -> IExpr a
inc (ICon i c@(ICInt { iVal = il@(IntLit { ilValue = n }) })) =
    -- GHC emits a warning below because it's forgotten that 'c' must be
    -- an ICInt
    ICon i (c { iVal = il { ilValue = n+1 } })
inc iexpr = internalError ("ITransform.inc: " ++ ppString iexpr)

mkZero :: IType -> IExpr a
mkZero t = iMkLit (aitBit t) 0

-- only match non-chosen undefined values
isUndet :: IExpr a -> Bool
isUndet (ICon _ (ICUndet { imVal = Nothing })) = True
isUndet _ = False

-- Guard optimizations that are not valid in the presence of implicit conditions.
noRefs :: IExpr a -> Bool
noRefs (IRefT {})    = False
noRefs (IAps f _ es) = all noRefs (f:es)
noRefs _             = True

isIfElseOfIConInt :: IExpr a -> Bool
isIfElseOfIConInt (IAps (ICon _ (ICPrim _ PrimIf)) [t] [cnd, thn, els]) =
    isIfElseOfIConInt' thn && isIfElseOfIConInt' els
  where
    isIfElseOfIConInt' (IAps (ICon _ (ICPrim _ PrimIf)) [t] [cnd, thn, els]) =
        isIfElseOfIConInt' thn && isIfElseOfIConInt' els
    isIfElseOfIConInt' (ICon _ (ICValue { iValDef = e })) =
        isIfElseOfIConInt' e
    isIfElseOfIConInt' e = isIConInt e || isUndet e
isIfElseOfIConInt (ICon _ (ICValue { iValDef = e })) = isIfElseOfIConInt e
isIfElseOfIConInt _ = False

isConstExprForPrim :: PrimOp -> IExpr a -> Bool
isConstExprForPrim prim (IAps (ICon _ (ICPrim _ p)) _ [e1,e2]) =
    (p == prim) && ((isIConInt e1) || (isIConInt e2))
isConstExprForPrim _ _ = False

constPart :: IExpr a -> IExpr a
constPart (IAps (ICon _ (ICPrim _ p)) _ [e1,e2])
    | isIConInt e1 = e1
    | isIConInt e2 = e2
    | otherwise    = internalError "constPart: no const part found!"
constPart _ = internalError "constPart: expected a binary primitive op"

nonConstPart :: IExpr a -> IExpr a
nonConstPart (IAps (ICon _ (ICPrim _ p)) _ [e1,e2]) =
    if (isIConInt e1) then e2 else e1  -- note: e2 may also be a constant!
nonConstPart _ = internalError "nonConstPart: expected a binary primitive op"

-- More accurate (and faster) equality by ignoring ICValue
eqE :: IExpr a -> IExpr a -> Bool
eqE (IAps e1 ts1 es1)                    (IAps e2 ts2 es2)                    = eqE e1 e2 && ts1 == ts2 && and (zipWith eqE es1 es2)
eqE (ICon i1 (ICValue { iValDef = e1 })) (ICon i2 (ICValue { iValDef = e2 })) = i1 == i2
eqE (ICon _  (ICValue { iValDef = e1 }))                               e2     = eqE e1 e2
eqE                               e1     (ICon _  (ICValue { iValDef = e2 })) = eqE e1 e2
eqE                               e1                                   e2     = e1 == e2

-----------------------------------------------------------------------------

data TState a = TState {
        errHandle :: ErrorHandle,
        flags :: Flags,

        -- Prefix to use for generating new names (resulting from CSE)
        prefix :: String,
        -- Source of unique numbers to append to generated names
        idNo :: Integer,

        -- A map of package defs.  When ICValue is encountered, the def is
        -- looked up in this map and the assigned expression is inlined.
        -- The defprops are kept to be used in the fixup step that happens
        -- between processing defs and processing the rest of the module.
        def_map :: M.Map Id (IType, IExpr a, [DefProp]),

        -- A CSE map, from an expr "e" to a tuple of info for the canonical
        -- def ("defname") to represent it:
        --   * an expr to use to refer to the def ("ICValue defname")
        --   * the def ("IDef defname deftype e")
        -- When the monad is run, because all exprs are inlined and then CSE'd
        -- back up, the defs for the package will come from this map.
        cse_map :: M.Map (IExpr a) (IExpr a, IDef a)
        }

type T b a = State (TState a) b

runT :: ErrorHandle -> Flags -> Integer -> String -> T b a -> (b, [IDef a])
runT errh flags no prefix xforms =
    let initState :: TState a
        initState = TState { errHandle = errh
                           , flags = flags
                           , prefix = prefix
                           , idNo = no
                           , def_map = M.empty
                           , cse_map = M.empty
                           }
    in case runState xforms initState of
         (x, ts) ->
              let defs_from_cse = map (snd . snd) (M.toList (cse_map ts))
                  non_cse_defs =
                      [ IDef i t e props
                        | (i, (t, e, props)) <- M.toList (def_map ts)
                        , defPropsHasNoCSE props
                      ]
                  defs = defs_from_cse ++ non_cse_defs
              in  (x, defs)

getDoBO :: T Bool a
getDoBO = do
  flgs <- gets flags
  return (optBool flgs)

-- Create a CSE def for an expression, returning a reference;
-- if a def already exists for this expression, return the existing reference.
newExprT :: IType -> IExpr a -> T (IExpr a) a
newExprT t e = do
  ts <- get
  cmap <- gets cse_map
  case (M.lookup e cmap) of
    Just (e', _) -> return e'
    Nothing -> do
        n <- gets idNo
        let i = setBadId $ mkId noPosition (mkFString ((prefix ts) ++ itos n))
            e' = ICon i (ICValue t e)
            d = IDef i t e []  -- props get lost here, but restored in iTransRenameIdsInDef
        put $ ts { idNo = n+1, cse_map = M.insert e (e', d) cmap }
        -- traceM ("newExprT " ++ ppString e ++ " -> " ++ ppString (e',d))
        return e'

addDefT :: Id -> IType -> IExpr a -> [DefProp] -> T () a
addDefT i t e p = do
  -- traceM $ "addDefT " ++ ppString i ++ " " ++ ppString e
  ts <- get
  put $ ts {def_map = M.insert i (t,e,p) (def_map ts) }

getDefT :: Id -> T (Maybe (IExpr a)) a
getDefT i = get >>= (return . fmap snd3 . M.lookup i . def_map)

{- we don't need uEq because we use a progress check instead now
-- the uEq check is tuned to what we need to do to fix
-- concats including undefined values correctly
-- things are uEq if:
--  - they are directly equal
--  - they are equal if you expand chosen undefined values
--  - where they are not equal one part is an unchosed undefined value
-- as in eqE, we don't go inside ICValue when the names are equal
-- this avoids some stack overflows and other nastiness
uEq :: IExpr a -> IExpr a -> Bool
uEq e1 e2 = {- trace ("uEq: " ++ ppReadable (e1, e2)) $ -} uEq' e1 e2
uEq' (ICon _ (ICUndet { imVal = Nothing })) e = True
uEq' e (ICon _ (ICUndet { imVal = Nothing })) = True
uEq' e1 (ICon _ (ICUndet { imVal = Just e2 })) = uEq e1 e2
uEq' (ICon _ (ICUndet { imVal = Just e1 })) e2 = uEq e1 e2
uEq' (ICon i1 (ICValue { })) (ICon i2 (ICValue { })) = i1 == i2
uEq' (ICon _ (ICValue _ e1)) e2 = uEq e1 e2
uEq' e1 (ICon _ (ICValue _ e2)) = uEq e1 e2
uEq' (IAps (ICon _ (ICPrim _ PrimIf)) _ [c1,t1,e1]) (IAps (ICon _ (ICPrim _ PrimIf)) _ [c2,t2,e2]) =
    (c1 `eqE` c2 && t1 `uEq` t2 && e1 `uEq` e2) ||
    (t1 `uEq` e1 && t2 `uEq` e2 && t1 `uEq` t2)
uEq' (IAps (ICon _ (ICPrim _ PrimIf)) _ [_,t1,e1]) e2 = t1 `uEq` e2 && e1 `uEq` e2
uEq' e1 (IAps (ICon _ (ICPrim _ PrimIf)) _ [_,t2,e2]) = e1 `uEq` t2 && e1 `uEq` e2
uEq' e1 e2 = e1 == e2
-}

-----------------------------------------------------------------------------

optBoolExpr :: Bool -> IExpr a -> IExpr a
optBoolExpr moreBoolOpt = optBoolExprN 8 moreBoolOpt

optBoolExprN :: Int -> Bool -> IExpr a -> IExpr a
optBoolExprN nvars moreBoolOpt =
        fromBE .
        (if moreBoolOpt then tryHard nvars else sSimplify) .
        toBE .
        (if moreBoolOpt then aOptCmp else sOptCmp) .
        expValAndOrCmp

tryHard :: Int -> BoolExp (IExpr a) -> BoolExp (IExpr a)
tryHard nvars e =
        case optBoolExprQM nvars e of                -- Don't try more than 8 variables.
        Nothing -> {-trace ("tryHard too big " ++ ppReadable e) $ -} aSimplify e
        Just e' -> {-trace (ppReadable(e, e')) -} e'

fromBE :: BoolExp (IExpr a) -> IExpr a
fromBE (And e1 e2)   = ieAnd (fromBE e1) (fromBE e2)
fromBE (Or  e1 e2)   = ieOr  (fromBE e1) (fromBE e2)
fromBE (Not e)       = ieNot (fromBE e)
fromBE (If e1 e2 e3) = ieIf itBit1 (fromBE e1) (fromBE e2) (fromBE e3)
fromBE (Var e)       = e
fromBE TT            = iTrue
fromBE FF            = iFalse

toBE :: IExpr a -> BoolExp (IExpr a)
toBE (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2])   = And (toBE e1) (toBE e2)
toBE (IAps (ICon _ (ICPrim _ PrimBOr))  _ [e1, e2])   = Or  (toBE e1) (toBE e2)
toBE (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e])        = Not (toBE e)
toBE (IAps (ICon _ (ICPrim _ PrimIf))   _ [e1,e2,e3]) = If (toBE e1) (toBE e2) (toBE e3)
toBE e | e == iTrue  = TT
       | e == iFalse = FF
       | otherwise   = Var e

-- A quick hack for optimizing comparisons
sOptCmp :: IExpr a -> IExpr a
sOptCmp e =
    let collEQs (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = collEQs e1 ++ collEQs e2
        collEQs (IAps (ICon _ (ICPrim _ PrimEQ))   _ [v, ICon _ (ICInt { iVal = IntLit { ilValue = i } })]) = [(v, i)]
        collEQs _ = []
        remNE vcs e@(IAps (ICon _ (ICPrim _ PrimEQ))   _ [v, ICon _ (ICInt { iVal = IntLit { ilValue = i } })]) =
                case lookup v vcs of
                Just i' | i /= i' -> iFalse
                _ -> e
        remNE vcs (IAps f ts es) = IAps f ts (map (remNE vcs) es)
        remNE vcs e = e

        collTerms (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = collTerms e1 ++ collTerms e2
        collTerms e = [e]

        remAbsurd e (IAps (ICon _ (ICPrim _ PrimBNot)) _
                        [IAps (ICon _ (ICPrim _ PrimEQ)) _
                                [v, ICon _ (ICInt { iConType = ITAp bit (ITNum vn), iVal = IntLit { ilValue = i } })]] : es)
                | bit == itBit && vn <= 8 = loop ([0..2^vn-1] \\ [i]) es
                  where loop [] [] = iFalse
                        loop _  [] = e
                        loop is (IAps (ICon _ (ICPrim _ PrimBNot)) _ [IAps (ICon _ (ICPrim _ PrimEQ)) _ [v', ICon _ (ICInt { iVal = IntLit { ilValue = i } })]] : es)
                                | v == v' = loop (is \\ [i]) es
                        loop is (_:es) = loop is es
        remAbsurd e (_:es) = remAbsurd e es
        remAbsurd e [] = e

        remAbs e = remAbsurd e (collTerms e)

    in  remAbs (remNE (collEQs e) e)

aOptCmp :: IExpr a -> IExpr a
aOptCmp e =
        --trace ("optCmp:\n" ++ ppReadable e) $
        let (_, e') = optE M.empty e
        in  --(if e/=e' then traces (ppReadable (e, e')) else id)
            e'

optE :: ValMap a -> IExpr a -> (ValMap a, IExpr a)
optE m e0@(IAps p@(ICon _ (ICPrim _ PrimBAnd)) ts [e1, e2]) =
-- XXX this can't be the best way
        let (m1, e2') = optE m  e2
            (m2, e1') = optE m1 e1
        in  if e1 /= e1' then
                (m2, IAps p ts [e1', e2'])
            else
                let (m1, e1') = optE m  e1
                    (m2, e2') = optE m1 e2
                in  (m2, IAps p ts [e1', e2'])
optE m e@(IAps p@(ICon _ (ICPrim _ cmp)) _ [v, ICon _ (ICInt { iConType = t, iVal = IntLit { ilValue = i } })])
  | isCmp cmp
  , (Just n) <- getBit t
  = doCmp m e cmp v n i True
optE m e@(IAps (ICon _ (ICPrim _ PrimBNot)) _
                [IAps p@(ICon _ (ICPrim _ cmp)) ts [v, ICon _ (ICInt { iConType = t, iVal = IntLit { ilValue = i } })]])
  | isCmp cmp
  , (Just n) <- getBit t
  = doCmp m e cmp v n i False
optE m e =
        case vsGetSingleton e m of
        Nothing -> (m, e)
        Just i -> (m, iMkLit (iGetType e) i)

type ValMap a = M.Map (IExpr a) ValueSet

vmAdd :: IExpr a -> ValueSet -> ValMap a -> ValMap a
vmAdd k vs m = M.insert k vs m

vmGet :: IExpr a -> ValMap a -> ValueSet
vmGet v m =
    case M.lookup v m of
    Just vs -> vs
    Nothing -> vsUniv v

---

type ValueSet = VSetInteger

vsUniv :: IExpr a -> ValueSet
vsUniv (ICon i (ICValue { iValDef = IAps (ICon _ (ICPrim _ PrimRange)) _
                                        [ICon _ (ICInt { iVal = IntLit { ilValue = lo } }), ICon _ (ICInt { iVal = IntLit { ilValue = hi } }), _] })) =
        --traces ("interval " ++ ppReadable (i,lo,hi)) $
        vFromTo lo hi
vsUniv e =
        --traces ("nointerval " ++ ppReadable e) $
        case getBit (iGetType e) of
        Just n  -> vFromTo 0 (2^n-1)
        Nothing -> internalError "vsUniv"

vsGetSingleton :: IExpr a -> ValMap a -> Maybe Integer
vsGetSingleton e m = M.lookup e m >>= vGetSing

isCmp :: PrimOp -> Bool
isCmp PrimEQ = True
isCmp PrimULT = True
isCmp PrimULE = True
isCmp _      = False

cmpToVS :: Integer -> Integer -> Bool -> PrimOp -> VSetInteger
cmpToVS n i True  PrimEQ  = vSing i
cmpToVS n i True  PrimULT = vFromTo 0 (i-1)
cmpToVS n i True  PrimULE = vFromTo 0 i
cmpToVS n i False PrimEQ  = vFromTo 0 (i-1) `vUnion` vFromTo (i+1) (2^n-1)
cmpToVS n i False PrimULT = vFromTo (i+1) (2^n-1)
cmpToVS n i False PrimULE = vFromTo i (2^n-1)
cmpToVS _ _ _     prim    =
    internalError ("ITransform.cmpToVS: " ++ ppString prim)

doCmp :: ValMap a -> IExpr a -> PrimOp -> IExpr a -> Integer -> Integer -> Bool -> (ValMap a,IExpr a)
doCmp m e cmp v n i norm =
        let vs = vmGet v m
            tvs = cmpToVS n i norm cmp
            fvs = cmpToVS n i (not norm) cmp
            vs' = vs `vIntersect` tvs
            ivs = vs `vIntersect` fvs
            m' = vmAdd v vs' m
        in  if vNull ivs && not (vNull vs') then
                (m', iTrue)
            else if vNull vs' && not (vNull ivs) then
                (m', iFalse)
            else
                (m', e)

getBit :: IType -> Maybe Integer
getBit (ITAp b (ITNum n)) | b == itBit = Just n
getBit _ = Nothing

-----------------------------------------------------------------------------

-- After transforming the defs, with no prior CSE assumptions,
-- we digest the resulting CSE info and use that as the assumptions
-- when transforming the rest of the module.
--
-- We find all the defs that were CSE'd to the same (bad) new name and
-- replace it with a good name from one of the defs (if there is one).
-- Some of these defs are marked as not-CSE-able, so we keep those defs
-- separate.
--
iTransFixupDefNames :: forall a . Flags -> T () a
iTransFixupDefNames flags = do
  transform_state <- get
  let
      old_defmap = def_map transform_state
      old_csemap = cse_map transform_state

      -- A map from (bad) CSE names to the defs that it replaced
      -- (from those defs, we'll want to pick a good name, to keep)
      -- (and attempt to preserve the defprops?)
      cse_ids_map :: M.Map Id [(Id, [DefProp])]
      cse_ids_map =
          M.fromListWith (++) $
               [ (cse_name, [(def_name, props)])
                 | (def_name, (_, ICon cse_name value@(ICValue {}), props))
                       <- M.toList old_defmap ]

      -- Identify the name to be used, by filtering out the non-CSE defs
      -- and picking the best name from the remaining (for now, the first)
      rename_map =
          let pickId cse_id def_ips =
                  -- filter out the non-CSE defs
                  case (filter (not . defPropsHasNoCSE . snd) def_ips) of
                    -- if they're all non-CSE, keep the bad name
                    [] -> cse_id
                    -- otherwise, take the first def name
                    ((def_id, _):_) -> def_id
          in  M.mapWithKey pickId cse_ids_map

      -- function to rename ICValue references (to use the new CSE name)
      rename_expr = iTransRenameIdsInExpr rename_map

      -- function to rename a CSE def
      -- XXX defprops from the CSE'd defs are lost
      rename_def = iTransRenameIdsInDef rename_map

      -- fixup the CSE Map so that:
      --    * refs in the expr should refer to the new CSE name
      --    * the CSE ref should point to the new CSE name
      --    * the def name and expr are updated
      new_csemap =
          M.fromList
               [ (rename_expr e, (rename_expr ref, rename_def def))
                 | (e, (ref, def)) <- M.toList old_csemap ]

      -- fix up the defs to refer to new CSE name in their exprs
      -- (the def names themselves are unchanged)
      new_defmap =
          let mapFn (ty, e, props) = (ty, rename_expr e, props)
          in  M.map mapFn old_defmap

      new_state :: TState a
      new_state = transform_state { def_map = new_defmap,
                                    cse_map = new_csemap }
  put new_state

-- given a map from old to new identifiers, replace all occurrences
-- of the old identifier with the new in a given expression
iTransRenameIdsInExpr :: M.Map Id Id -> IExpr a -> IExpr a
iTransRenameIdsInExpr rename_map expr@(ICon name value@(ICValue {})) =
    let renamed_value_def = iTransRenameIdsInExpr rename_map (iValDef value)
        new_value = value { iValDef = renamed_value_def }
    in  ICon (iTransRenameId rename_map name) new_value
iTransRenameIdsInExpr rename_map (IAps func types args) =
    let renamed_func = iTransRenameIdsInExpr rename_map func
        renamed_args = [iTransRenameIdsInExpr rename_map arg | arg <- args]
    in  IAps renamed_func types renamed_args
iTransRenameIdsInExpr rename_map (ICon i (ICUndet t k (Just v))) =
    let v' = iTransRenameIdsInExpr rename_map v
    in ICon i (ICUndet t k (Just v'))
iTransRenameIdsInExpr rename_map expr = expr

-- given a map from old to new identifiers, replace all occurrences
-- of the old identifier with the new in a given definition,
-- including the name being defined
-- XXX This loses the props.  If the name is not renamed, we can keep
-- XXX the old props; if it's renamed, we need to be given the new props.
iTransRenameIdsInDef :: M.Map Id Id -> IDef a -> IDef a
iTransRenameIdsInDef rename_map (IDef name typ expr _) =
    let renamed_expr = iTransRenameIdsInExpr rename_map expr
        renamed_name = iTransRenameId rename_map name
    in  IDef renamed_name typ renamed_expr []

-- given a map from old to new identifiers, replace any old id with a new one
iTransRenameId :: M.Map Id Id -> Id -> Id
iTransRenameId rename_map name = M.findWithDefault name name rename_map

-----------------------------------------------------------------------------
