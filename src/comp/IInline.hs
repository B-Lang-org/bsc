module IInline(iInline, iSortDs, iInlineFmts) where
import Data.List(group, sort, nub)
import Util
import qualified Data.Set as S
import qualified Data.Map as M
import SCC(tsort)
import PPrint
import ErrorUtil
import ISyntax
import ISyntaxUtil(irulesMap, itFmt, iGetType, iDefsMap, emptyFmt);
import Id
import Prim
import Data.Maybe(catMaybes)
-- import Debug.Trace(trace)


iInline :: Bool -> IModule a -> IModule a
iInline inlSimp = iInline1 . iInlineS inlSimp -- . iSortDs
--iInline inlSimp = iInlineAll

-- Sort definitions in dependency order
iSortDs :: IModule a -> IModule a
iSortDs imod@(IModule { imod_local_defs = ds }) =
    let g = [(i, fdVars e) | IDef i _ e _ <- ds ]
        m = M.fromList [(i, d) | d@(IDef i _ _ _) <- ds]
        get i = case M.lookup i m of
                Nothing -> internalError ("iSortDs: lookup: " ++ ppReadable i)
                Just d -> d
        ds' = case tsort g of
                Left iss -> internalError ("iSortDs: cyclic definition: " ++ ppReadable iss)
                Right is -> map get is
    in  imod { imod_local_defs = ds' }


inline_ifc :: M.Map Id (IExpr a) -> M.Map Id (IExpr a) -> IEFace a -> IEFace a
inline_ifc smap dmap (IEFace i xs me mrs wp fi) = IEFace i xs me' mrs' wp fi
  where me'  = fmap (\(e, t) -> (iSubst smap dmap e, t)) me
        mrs' = fmap (irulesMap (iSubst smap dmap)) mrs

-- Inline definitions that are simple
iInlineS :: Bool -> IModule a -> IModule a
iInlineS False m = m
iInlineS True imod@(IModule { imod_local_defs = ds,
                              imod_rules      = rs,
                              imod_interface  = ifc}) =
    let smap = M.fromList [ (i, iSubst smap dmap e) | IDef i _ e _ <- ds, not (isKeepId i), simple e ]
        ds' = iDefsMap (iSubst smap dmap) ds
        dmap = M.fromList [ (i, e) | IDef i t e _ <- ds' ]
        ifc' = map (inline_ifc smap dmap) ifc
        rs' = irulesMap (iSubst smap dmap) rs
        state_vars' = [ (name, sv { isv_iargs = es' })
                      | (name, sv@(IStateVar { isv_iargs = es }))
                            <- imod_state_insts imod,
                        let es' = map (iSubst smap dmap) es ]
        -- concatenation and bit selection are just wires, inline them
        -- this is to improve the performance of the ITransform pass
        -- ITransform should re-CSE anything that it does not simplify
        simple (IAps (ICon _ (ICPrim _ PrimConcat)) _ [e1, e2]) = simple e1 && simple e2
        simple (IAps (ICon _ (ICPrim _ PrimSelect)) _ [e]) = simple e
        simple (IAps (ICon _ (ICPrim _ PrimExtract)) _ [e1,e2,e3]) = simple e1 && simple e2 && simple e3
        -- boolean expressions are just gates, inline them
        simple (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = simple e1 && simple e2
        simple (IAps (ICon _ (ICPrim _ PrimBOr)) _ [e1, e2]) = simple e1 && simple e2
        simple (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = simple e
        -- these are noops, inline them
        simple (ICon _ (ICMethArg { })) = True
        simple (ICon _ (ICModPort { })) = True
        simple (ICon _ (ICModParam { })) = True
        simple (ICon _ (ICStateVar { })) = True
        simple (ICon _ (ICValue { })) = True
        simple (ICon _ (ICInt { })) = True
        simple (ICon _ (ICReal { })) = True
        --
        simple _ = False

    in  imod { imod_local_defs  = ds',
               imod_rules       = rs',
               imod_interface   = ifc',
               imod_state_insts = state_vars' }

ruleVars :: IRules a -> [Id]
ruleVars (IRules sps rs) = concatMap leafVars rs
    where leafVars r = iValVars (irule_pred r) ++ iValVars (irule_body r)

varVars :: (a, IStateVar b) -> [Id]
varVars (_, IStateVar { isv_iargs = es }) =
        let vs = concatMap iValVars es
        in  vs ++ vs                -- XXX

-- Inline definitions used once
iInline1 :: IModule a -> IModule a
iInline1 = iInlineUseLimit 1

-- iInlineAll :: IModule a -> IModule a
-- iInlineAll = iInlineUseLimit 100000

iInlineUseLimit :: Int -> IModule a -> IModule a
iInlineUseLimit use_limit
                imod@(IModule { imod_state_insts = itvs,
                                imod_local_defs  = ds,
                                imod_rules       = rs,
                                imod_interface   = ifc }) =
    let ifcRuleVars = concatMap ruleVars (catMaybes [ mrs | IEFace _ _ _ mrs _ _ <- ifc ])
        is = [ i | (IEFace i _ (Just (e, _)) _ _ _) <- ifc ]
             ++ ruleVars rs
             ++ concatMap varVars itvs
             ++ ifcRuleVars
             ++ [ i | (IDef i _ _ _) <- ds, keepEvenUnused i]
        keepEvenUnused :: Id -> Bool
        keepEvenUnused i = hasIdProp i IdP_keepEvenUnused
        defids = S.fromList [ i | IDef i _ _ _ <- ds ]
        dm = M.fromList ([(i, e) | IDef i _ e _ <- ds ] ++
                         [ (i, e) | (IEFace i _ (Just (e,_)) _ _ _) <- ifc ])
        get i = case M.lookup i dm of (Just e) -> e; _-> internalError ("iInlineUseLimit " ++ ppString use_limit ++ ": " ++ ppReadable i)
        step allIds done [] = allIds
        step allIds done (i:pend) =
                if i `S.member` done then
                    step allIds done pend
                else
                    let is = iValVars (get i)
                    in  -- trace ("add " ++ ppReadable (i, is)) $
                        step (is ++ allIds) (S.insert i done) (nub is ++ pend)
        dis = step is S.empty (remOrdDup (sort is))
        ics = [ (i, length is) | is@(i:_) <- group (sort dis), i `S.member` defids ]
        onemap = M.fromList [ (i, iSubst onemap dmap (get i))
                             | (i, n_uses) <- ics, not (isKeepId i),
                               n_uses <= use_limit ]
        ds' = iDefsMap (iSubst onemap dmap) ds
        ifc' = map (inline_ifc onemap dmap) ifc
        rs' = irulesMap (iSubst onemap dmap) rs
        uses = M.fromList ics
        getc' i = M.findWithDefault 0 i uses
        getc i = {- trace ("getc: " ++ ppReadable (i, getc' i)) $ -} getc' i
        ds'' = filter (\ (IDef i _ _ _) ->
                        let uses = getc i in
                        (keepEvenUnused i || uses > 0 && isKeepId i)
                        || uses > use_limit) ds'
        dmap = M.fromList [(i, e) | IDef i t e _ <- ds']
        state_vars' = [ (name, sv { isv_iargs = es' })
                      | (name, sv@(IStateVar { isv_iargs = es }))
                            <- imod_state_insts imod,
                        let es' = map (iSubst onemap dmap) es ]
        new_imod = imod { imod_local_defs = ds'',
                          imod_rules = rs',
                          imod_interface = ifc',
                          imod_state_insts = state_vars' }
    in new_imod

iValVars :: IExpr a -> [Id]
iValVars (IAps e _ es) = iValVars e ++ concatMap iValVars es
iValVars (ICon i (ICValue { })) = [i]
iValVars (ICon i (ICUndet {imVal = Just e})) = iValVars e
iValVars (ICon _ _) = []
iValVars e = internalError ("iValVars: " ++ ppReadable e)

iSubst :: (M.Map Id (IExpr a)) -> (M.Map Id (IExpr a)) -> IExpr a -> IExpr a
iSubst subMap defMap e = sub e
  where sub (IAps f ts es) = IAps (sub f) ts (map sub es)
        sub d@(ICon i val@(ICValue {})) =
            case M.lookup i subMap of
            Nothing ->
              let ev = fromJustOrErr ("IInline.iSubst ICValue def not found: " ++ ppReadable i)
                                     (M.lookup i defMap)
              in ICon i (val { iValDef = ev })
            Just e -> e
        sub u@(ICon i (ICUndet t k (Just v))) = ICon i (ICUndet t k (Just (sub v)))
        sub c@(ICon {}) = c
        sub ee = internalError ("iSubst: " ++ ppReadable ee)

iSubst' :: ((IExpr a) -> Bool) -> (M.Map Id (IExpr a)) -> (M.Map Id (IExpr a)) -> IExpr a -> IExpr a
iSubst' tst subMap defMap e = sub e
  where sub (IAps f ts es) = IAps (sub f) ts (map sub es)
        sub d@(ICon i val@(ICValue {})) =
            case M.lookup i subMap of
            Nothing ->
              let ev = fromJustOrErr ("IInline.iSubst' ICValue def not found: " ++ ppReadable i)
                                     (M.lookup i defMap)
              in ICon i (val { iValDef = ev })
            Just e -> if (tst e) then e else d
        sub u@(ICon i (ICUndet t k (Just v))) = ICon i (ICUndet t k (Just (sub v)))
        sub c@(ICon {}) = c
        sub ee = internalError ("iSubst': " ++ ppReadable ee)

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
    let smap = M.fromList [ (i, iSubst' tst smap dmap e) | IDef i t e _ <- ds, (t == itFmt) ] -- inline any def of type Fmt
        ds' = iDefsMap (iSubst' tst smap dmap) ds
        dmap = M.fromList [ (i, e) | IDef i t e _ <- ds' ]
        ifc' = map (inline_ifc smap dmap) ifc
        rs' = irulesMap (iSubst' tst smap dmap) rs
        state_vars' = [ (name, sv { isv_iargs = es' })
                      | (name, sv@(IStateVar { isv_iargs = es }))
                            <- imod_state_insts imod,
                        let es' = map (iSubst' tst smap dmap) es ]
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
-- pMatch (IAps (ICon fid0 (ICForeign {iConType = t0})) [] [e0]) (IAps (ICon fid1 (ICForeign {iConType = t1})) [] [e1])
--        | fid0 == fid1 && pMatch e0 e1 = True
-- pMatch e0 e1 = e0 == e1

-- #############################################################################
-- #
-- #############################################################################

-- zshow   (IAps (ICon _ (ICPrim _ PrimFmtConcat)) _ [e0, e1]) = text "(FmtConcat "  <+> (zshow e0) <+> (zshow e1) <+> text ")"
-- zshow x@(IAps (ICon _ (ICPrim _ PrimIf)) _ [cond, e0, e1]) = text "(? " <> (zshow e0) <+> text " : " <+> (zshow e1) <+> text ")"
-- zshow   (IAps (ICon fid f@(ICForeign {fcallNo = n, iConType = ict})) ts es) = text (pfpString (unQualId fid)) <> text (show n) <> text "# (" <> sep (map zshow es) <> text ")"
-- zshow   (IAps _ _ [e]) | isAVFFWithFmts e = text("<ZZ ") <> (zshow e) <> text(">")
-- zshow   (IAps icJoinActions _ es@(a:b:rest))  = text("action { ") <> sep (map zshow es) <> text("} endaction")
-- zshow   (ICon _ ICString {iStr = xx}) = text ("\"" ++ xx ++ "\"")
-- zshow   x@(ICon i ICValue {}) = text ("<ref " ++ show i ++ " > ")
-- -- zshow x | (myGetType "K1") x == itFmt = text "<Fmt>"
-- -- zshow x | (myGetType "K1") x == itAction = text ("<Action> " ++ (show x))
-- -- zshow x | isitActionValue_ ((myGetType "K1") x) = text ("<ActionValue_> " ++ (show x))
-- zshow (IAps x ts es) = sep (map zshow es)
-- zshow x = text "<?>"
-- -- zshow x = text ("<?> " ++ ppReadable x)
-- -- zshow x = text (show x)
