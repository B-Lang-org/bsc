module CSyntaxTypes(
                    Types(..)
                    ) where

import Data.List(union, (\\), nub)
import Util(mapSnd)
import PPrint(ppReadable)
import ErrorUtil(internalError)
import Subst
import CSyntax

--import Debug.Trace


instance Types CDefn where
    apSub s (CValueSign d) = CValueSign (apSub s d)
    apSub s d = d
    tv (CValueSign d) = tv d
    tv d = []

instance Types CDef where
    apSub s (CDef i qt cs) = CDef i (apSub s qt) (apSub s cs)
    -- This line has been here since revision 1 with the comment "XXX vs ?"
    --apSub s (CDefT i vs qt cs) = CDefT i vs (apSub s qt) (apSub s cs)
    -- The "vs" are the lambda-bound type variables in this definition.
    -- Thus, substituting for or to them is an error.  (Unless the caller
    -- knows what he's doing?)
    -- Below, we remove these variables from the substitution.
    -- This fixes bug 675, but is it fixing the problem or just masking it?
    -- More thought/investigation is needed.
    apSub s (CDefT i vs qt cs) =
        let s' = if null vs then s else trimSubstByVars vs s
        in  CDefT i vs (apSub s' qt) (apSub s' cs)
{-
    -- For investigating, use this code to assert an internalError or trace
    -- on bad substitutions.
        let (s',removed_vs) = removeFromSubst vs s
            r = getSubstRange s'
        in
            --if (any (\v -> elem v r) removed_vs)
            if (any (\v -> elem v r) vs)
            then internalError ("apSub CDefT:\n" ++
                                " i = " ++ ppReadable i ++
                                " vs = " ++ ppReadable vs ++
                                " removed_vs = " ++ ppReadable removed_vs ++
                                " s' = " ++ ppReadable s')
            else
            if (length removed_vs > 0)
            then trace ("apSub CDefT, removing from Subst:\n" ++
                        " i = " ++ ppReadable i ++
                        " vs = " ++ ppReadable vs ++
                        " removed_vs = " ++ ppReadable removed_vs ++
                        " s = " ++ ppReadable s) $
                 CDefT i vs (apSub s' qt) (apSub s' cs)
            else CDefT i vs (apSub s' qt) (apSub s' cs)
-}
    tv (CDef i qt cs) = tv (qt, cs)
    tv (CDefT i vs qt cs) = (nub (tv (qt, cs))) \\ vs

instance Types CClause where
    apSub s (CClause ps qs e) = CClause (apSub s ps) (apSub s qs) (apSub s e)
    tv (CClause ps qs e) = tv (ps, qs, e)

instance Types CRule where
    apSub s (CRule rps mi qs e) = CRule rps (apSub s mi) (apSub s qs) (apSub s e)
    apSub s (CRuleNest rps mi qs rs) = CRuleNest rps (apSub s mi) (apSub s qs) (apSub s rs)
    tv (CRule rps mi qs e) = tv (mi, qs, e)
    tv (CRuleNest rps mi qs rs) = tv (mi, qs, rs)

instance Types CQual where
    apSub s (CQGen t p e) = CQGen (apSub s t) (apSub s p) (apSub s e)
    apSub s (CQFilter e) = CQFilter (apSub s e)
    tv (CQGen t p e) = tv (t, p, e)
    tv (CQFilter e) = tv e

instance Types CExpr where
    apSub s (CLam i e) = CLam i (apSub s e)
    apSub s (CLamT i t e) = CLamT i (apSub s t) (apSub s e)
    apSub s (Cletrec ds e) = Cletrec (apSub s ds) (apSub s e)
    apSub s (Cletseq ds e) = Cletseq (apSub s ds) (apSub s e)
    apSub s (CSelect e i) = CSelect (apSub s e) i
    apSub s (CSelectTT ti e i) = CSelectTT ti (apSub s e) i
    apSub s (CCon i es) = CCon i (apSub s es)
    apSub s (Ccase pos e as) = Ccase pos (apSub s e) (apSub s as)
    apSub s (CStruct mb ti fs) = CStruct mb ti (mapSnd (apSub s) fs)
    apSub s (CStructUpd e fs) = CStructUpd (apSub s e) (mapSnd (apSub s) fs)
    apSub s (Cwrite pos e v) = Cwrite pos (apSub s e) (apSub s v)
    apSub s e@(CAny {}) = e
    apSub s e@(CVar _) = e
    apSub s (CApply f es) = CApply (apSub s f) (apSub s es)
    apSub s (CTaskApply f es) = CTaskApply (apSub s f) (apSub s es)
    apSub s (CTaskApplyT f t es) = CTaskApplyT (apSub s f) (apSub s t) (apSub s es)
    apSub s e@(CLit _) = e
    apSub s (CBinOp e1 o e2) = CBinOp (apSub s e1) o (apSub s e2)
    apSub s (CHasType e t) = CHasType (apSub s e) (apSub s t)
    apSub s (Cif pos e1 e2 e3) = Cif pos (apSub s e1) (apSub s e2) (apSub s e3)
    apSub s (CSub pos e1 e2) = CSub pos (apSub s e1) (apSub s e2)
    apSub s (CSub2 e1 e2 e3) = CSub2 (apSub s e1) (apSub s e2) (apSub s e3)
    apSub s (CSubUpdate pos e_vec (e_h, e_l) e_rhs) =
        CSubUpdate pos (apSub s e_vec) (apSub s e_h, apSub s e_l) (apSub s e_rhs)
    apSub s (Cmodule pos is) = Cmodule pos (apSub s is)
    apSub s (Cinterface pos mi ds) = Cinterface pos mi (apSub s ds)
    apSub s (CmoduleVerilog m ui c r ses fs sch ps) = CmoduleVerilog (apSub s m) ui c r (mapSnd (apSub s) ses) fs sch ps
    apSub s (CForeignFuncC i wty) = CForeignFuncC i (apSub s wty)
    apSub s (Cdo r ss) = Cdo r (apSub s ss)
    apSub s (Caction pos ss) = Caction pos (apSub s ss)
    apSub s (Crules ps rs) = Crules ps (apSub s rs)
    apSub s (CTApply e ts) = CTApply (apSub s e) (apSub s ts)
    apSub s (CSelectT ti i) = CSelectT ti i
    apSub s (CStructT t fs) = CStructT (apSub s t) (mapSnd (apSub s) fs)
    apSub s (CCon1 ti i e) = CCon1 ti i (apSub s e)
    apSub s (CConT t i es) = CConT t i (apSub s es)
    apSub s (CLitT t l) = CLitT (apSub s t) l
    apSub s (CAnyT pos uk t) = CAnyT pos uk (apSub s t)
    apSub s (CmoduleVerilogT t m ui c r ses fs sch ps) =
        CmoduleVerilogT (apSub s t) (apSub s m) ui c r (mapSnd (apSub s) ses) fs sch ps
    apSub s (CForeignFuncCT i pty) = CForeignFuncCT i (apSub s pty)
    apSub s (COper os) = internalError ("CSyntaxTypes.Types(CExpr).apSub: COper " ++ ppReadable os)
    apSub s e@(Cattributes pps) = e
    apSub s e = internalError ("CSyntaxTypes.Types(CExpr).apSub: " ++ ppReadable e)

    tv (CLam i e) = tv e
    tv (CLamT i t e) = tv (t, e)
    tv (Cletrec ds e) = tv (ds, e)
    tv (Cletseq ds e) = tv (ds, e)
    tv (CSelect e i) = tv e
    tv (CSelectTT ti e i) = tv e
    tv (CCon i es) = tv es
    tv (Ccase pos e as) = tv (e, as)
    tv (CStruct _ _ fs) = tv (map snd fs)
    tv (CStructUpd e fs) = tv (e, map snd fs)
    tv (Cwrite pos e v) = tv (e,v)
    tv e@(CAny {}) = []
    tv e@(CVar _) = []
    tv (CApply f es) = tv (f, es)
    tv (CTaskApply f es) = tv (f, es)
    tv (CTaskApplyT f t es) = tv (f, t, es)
    tv e@(CLit _) = []
    tv (CBinOp e1 o e2) = tv (e1, e2)
    tv (CHasType e t) = tv (e, t)
    tv (Cif pos e1 e2 e3) = tv (e1, e2, e3)
    tv (CSub pos e1 e2) = tv (e1, e2)
    tv (CSub2 e1 e2 e3) = tv (e1, e2, e3)
    tv (CSubUpdate pos e_vec (e_h, e_l) e_rhs) = tv [e_vec, e_h, e_l, e_rhs]
    tv (Cmodule pos is) = tv is
    tv (Cinterface pos mi ds) = tv ds
    tv (CmoduleVerilog m ui c r ses fs sch ps) = tv (m, map snd ses)
    tv (CForeignFuncC i wty) = tv wty
    tv (Cdo r ss) = tv ss
    tv (Caction pos ss) = tv ss
    tv (Crules ps rs) = tv rs
    tv (CTApply e ts) = tv (e, ts)
    tv (CSelectT ti i) = []
    tv (CStructT t fs) = tv (t, map snd fs)
    tv (CCon1 ti i e) = tv e
    tv (CConT t i es) = tv es
    tv (CLitT t l) = tv t
    tv e@(CAnyT _ _ t) = tv t
    tv (CmoduleVerilogT t m ui c r ses fs sch ps) = tv (t, m, map snd ses)
    tv (CForeignFuncCT i pty) = tv pty
    tv (COper os) = internalError ("CSyntaxTypes.Types(CExpr).apSub: COper " ++ ppReadable os)
    tv e@(Cattributes pps) = []
    tv e = internalError ("CSyntaxTypes.Types(CExpr).tv: " ++ ppReadable e)

instance Types CStmt where
    apSub s (CSBindT p name pprops t e) = CSBindT (apSub s p) name pprops (apSub s t) (apSub s e)
    apSub s (CSBind p name pprops e) = CSBind (apSub s p) name pprops (apSub s e)
    apSub s (CSletrec ds) = CSletrec (apSub s ds)
    apSub s (CSletseq ds) = CSletseq (apSub s ds)
    apSub s (CSExpr name e) = CSExpr name (apSub s e)
    tv (CSBindT p _ _ t e) = tv (p, t, e)
    tv (CSBind p _ _ e) = tv (p, e)
    tv (CSletrec ds) = tv ds
    tv (CSletseq ds) = tv ds
    tv (CSExpr _ e) = tv e


instance Types CMStmt where
    apSub s (CMStmt t) = CMStmt (apSub s t)
    apSub s (CMrules e) = CMrules (apSub s e)
    apSub s (CMinterface e) = CMinterface (apSub s e)
    apSub s (CMTupleInterface pos es) = CMTupleInterface pos (apSub s es)
    tv (CMStmt t) = tv t
    tv (CMrules e) = tv e
    tv (CMinterface e) = tv e
    tv (CMTupleInterface pos es) = tv es

instance Types CPat where
    apSub s (CPCon c ps) = CPCon c (apSub s ps)
    apSub s (CPstruct mb c fs) = CPstruct mb c (mapSnd (apSub s) fs)
    apSub s p@(CPVar i) = p
    apSub s (CPAs i p) = CPAs i (apSub s p)
    apSub s p@(CPAny {}) = p
    apSub s p@(CPLit l) = p
    apSub s p@(CPMixedLit {}) = p
    apSub s (CPCon1 ti c p) = CPCon1 ti c (apSub s p)
    apSub s (CPConTs ti c ts ps) = CPConTs ti c (apSub s ts) (apSub s ps)
    apSub s (CPOper os) = internalError ("CSyntaxTypes.Types(CPat).apSub: CPOper " ++ ppReadable os)
    tv (CPCon c ps) = tv ps
    tv (CPstruct _ _ fs) = tv (map snd fs)
    tv (CPVar p) = []
    tv (CPAs i p) = tv p
    tv (CPAny {}) = []
    tv (CPLit l) = []
    tv (CPMixedLit {}) = []
    tv (CPCon1 ti c p) = tv p
    tv (CPConTs ti c ts ps) = tv (ts, ps)
    tv (CPOper os) = internalError ("CSyntaxTypes.Types(CPat).tv: CPOper " ++ ppReadable os)

instance Types CDefl where
    apSub s (CLValueSign d me) = CLValueSign (apSub s d) (apSub s me)
    apSub s (CLValue i cs me) = CLValue i (apSub s cs) (apSub s me)
    apSub s (CLMatch p e) = CLMatch (apSub s p) (apSub s e)
    tv (CLValueSign d me) = tv (d, me)
    tv (CLValue i cs me) = tv (cs, me)
    tv (CLMatch p e) = tv (p, e)

instance Types CQType where
    apSub s (CQType ps t) = CQType (apSub s ps) (apSub s t)
    tv (CQType ps t) = tv ps `union` tv t

instance Types CPred where
    apSub s (CPred c ts) = CPred c (apSub s ts)
    tv (CPred _ ts) = tv ts

instance (Types t) => Types (Maybe t) where
    apSub s (Just t) = Just (apSub s t)
    apSub s Nothing = Nothing
    tv (Just t) = tv t
    tv Nothing = []

instance (Types a, Types b) => Types (a, b) where
    apSub s (a, b) = (apSub s a, apSub s b)
    tv (a, b) = tv a `union` tv b

instance (Types a, Types b, Types c) => Types (a, b, c) where
    apSub s (a, b, c) = (apSub s a, apSub s b, apSub s c)
    tv (a, b, c) = tv a `union` tv b `union` tv c

instance (Types a, Types b, Types c, Types d) => Types (a, b, c, d) where
    apSub s (a, b, c, d) = (apSub s a, apSub s b, apSub s c, apSub s d)
    tv (a, b, c, d) = tv a `union` tv b `union` tv c `union` tv d

instance Types CCaseArm where
    apSub subst arm =
        CCaseArm { cca_pattern = apSub subst (cca_pattern arm),
                   cca_filters = apSub subst (cca_filters arm),
                   cca_consequent = apSub subst (cca_consequent arm) }
    tv arm = tv (cca_pattern arm) `union` tv (cca_filters arm) `union`
             tv (cca_consequent arm)
