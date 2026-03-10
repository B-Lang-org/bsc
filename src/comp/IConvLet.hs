-- Package of utility functions used by iConvLet in IConv
module IConvLet(
                docycles, reorderDs, unpoly
            ) where

import qualified Data.List as List

import Util(mapSnd)
import FStringCompat(concatFString)
import PPrint(ppReadable)
--import PPring(ppString)
import Error(internalError, ErrMsg(..), ErrorHandle, bsErrorUnsafe)
import Position
import CSyntax
import CSyntaxUtil(mkPairType)
import Id
import PreStrings(fsDollar)
import PreIds(idPrimFst, idPrimSnd, idPrimPair)
-- import Debug.Trace


docycles :: ErrorHandle -> [CDefl] -> [[Id]] -> [CDefl]
docycles errh ds cycles =
    -- trace("docycles = " ++ (ppReadable cycles)) $
    concatMap (do_one_cyclegroup errh ds) cycles

do_one_cyclegroup :: ErrorHandle -> [CDefl] -> [Id] -> [CDefl]
do_one_cyclegroup errh original_ds is =
            let
                ds' = reorderDs original_ds is
                      -- we use reorderDs just as a lookup function;
                      -- we actually do not care too much what order
                      -- they come out

            in case ds' of
                 [] -> internalError ("iConvLet: empty cycle")
                 [_] -> internalError ("iConvLet: cycle of one element")
                 _ -> many_cycle errh ds'

type Pick_func = CExpr -> CExpr

-- examples of  "Pick_func" are fst, fst.snd, fst.snd.snd, ...


pick_func_list :: [CType] -> (CType,[Pick_func])
-- For a given size (defined by the length of the CType list),
-- this function returns a list of functions each of which "picks" the
-- Nth element out of a large tuple created out of primPairs.
-- For example, for size three, the list of functions returned
-- is [fst, fst.snd, snd.snd] where "." is the compose operator.

pick_func_list [] = internalError "pick_func_list : empty list"
pick_func_list [_] = internalError "pick_func_list : singleton"
pick_func_list [ft1,ft2] = (mkPairType ft1 ft2,
                            [(\x -> CApply (the_pick idPrimFst) [x]),
                             (\y -> CApply (the_pick idPrimSnd) [y])])
    where
          the_pick :: Id -> CExpr
          the_pick x = (CTApply (CSelectT idPrimPair x) [ft1, ft2])

pick_func_list (a:rest) = let (t_rest, p_rest) = pick_func_list rest
                              the_pick :: Id -> CExpr
                              the_pick x = CTApply (CSelectT idPrimPair x) [a,t_rest]
                              apply_the_pick :: Pick_func -> Pick_func
                              apply_the_pick f = let
                                  g x = f (CApply (the_pick idPrimSnd) [x])
                                        in g
                                           -- ((CApply (the_pick idPrimSnd)) . )
                              first x = CApply (the_pick idPrimFst) [x]
                          in
                             (mkPairType a t_rest,
                              first:
                              (map apply_the_pick  p_rest))

-- turns a list of expressions into a tuple expression
typed_pair_expr :: [(CExpr,CType)] -> CExpr
typed_pair_expr [] = internalError "typed_pair_expr : empty list"
typed_pair_expr [_] = internalError "typed_pair_expr : singleton"
typed_pair_expr [(e1, ft1), (e2, ft2)] = CStructT (mkPairType ft1 ft2)
                                          [(idPrimFst, e1), (idPrimSnd, e2)]
typed_pair_expr ((e,ty):rest) =
    let rest_e = typed_pair_expr rest
    in case rest_e of
         (CStructT rest_t _) -> CStructT (mkPairType ty rest_t)
                                [(idPrimFst, e), (idPrimSnd, rest_e)]
         _ -> internalError "typed_pair_expr . rest_e"

many_cycle :: ErrorHandle -> [CDefl] -> [CDefl]
{-
 Given a list of mutual recursive definitions: E.g.,
 let a = definition of "a" which calls ... b ...
     b = definition of "b" which calls ... c ...
     c = definition of "c" which calls ... a ...

return a definition such that it is a singly recursive tuple,
and everything else "indexes" into the tuple.

 let a$b$c = ...
     a     = first a$b$c
     b     = second a$b$c
     c     = third a$b$c

The "first", "second", "third", etc., are the pick_func_list.

Then, deal_with_cycles above feeds these singly recursive things
back into iConvLet which applies primFix to them.

a$b$c is defined

let a$b$c = let a     = first a$b$c
                b     = second a$b$c
                c     = third a$b$c
            in ( definition of "a" ... b ...
               , definition of "b" ... c ...
               , definition of "c" ... a ...
               )

where the "a", "b", and "c" mask the "outer" definitions of them and
allow the original expressions that defined "a" "b" and "c" to be used
unchanged.  Somewhat miraculously, this construction (variables, e.g.,
"a", bound inside a "let" referring to the function within which it
defined, e.g., "a$b$c") does not count as mutual recursion.

-}

many_cycle errh ds@(d1:_) =
{-    trace ("many_cycle:\n" ++ (ppReadable ds)
           ++ "\n"
           ++ (ppReadable answer)
           ++ "----------- /many_cycle") $ -}
    answer:pick_defs
    where answer :: CDefl
          answer = CLValueSign def quals
          def :: CDef
          def = CDefT def_id def_tvars def_qtype def_clauses
              where
                def_tvars :: [TyVar]
                -- Might need to do renaming of type variables? XXX
                -- For now, if anything goes horribly wrong, we are going to
                -- rely on ISyntaxCheck to error out.
                def_tvars = -- trace_answer (\x -> "tvars " ++ (ppReadable x)) $
                            concatMap get_tvars ds -- ??
                def_qtype :: CQType
                -- Dropping the type contexts (they should be dealt with now).
                -- Might break for local mutual recursion that's polymorphic
                -- (because takes as arguments dictionaries that fails the
                -- later check: EMutualRecursionComplicatedClause)
                -- See testcase "Letrect.bs"
                def_qtype = CQType [] (fst picks)
                def_clauses :: [CClause]
                def_clauses = [CClause [] [] def_expr]
                def_expr :: CExpr
                -- these "inner" pick_defs shadow the "outer" ones and are used
                -- by the tuple itself.  In this way we avoid mutual recursion.
                def_expr = Cletrec pick_defs inner_expr
                inner_expr :: CExpr
                inner_expr = typed_pair_expr (zip (map get_expression ds)
                                                  types)
          quals :: [CQual]
          quals = concatMap get_quals ds

          get_type :: CDefl -> CType
          get_type (CLValueSign (CDefT _ _ (CQType _ t) _ ) _ ) = t
          get_type _ = internalError ("many_cycle . get_type")
          get_id :: CDefl -> Id
          get_id (CLValueSign (CDefT i _ _ _ ) _ ) = i
          get_id _ = internalError ("many_cycle . id")
          get_tvars :: CDefl -> [TyVar]
          get_tvars (CLValueSign (CDefT _ vs _ _) _) = vs
          get_tvars _ = internalError "many_cycle . get_tvars"
          get_expression :: CDefl -> CExpr
          get_expression d@(CLValueSign (CDefT _ _ _ clauses) _) =
              case clauses of
                [(CClause [] [] e)] -> e
                _ -> bsErrorUnsafe errh
                     [(getPosition d,
                       EMutualRecursionComplicatedClause (ppReadable (get_id d)))]
                     -- Desugaring makes this error case happen less frequently
                     -- than expected.  For example:
    {-
five :: Integer
five = let evens :: Integer -> List Integer
           evens x = cons x (map ((+) 1) odds)
           odds  :: List Integer = map ((+) 1) (evens 101)
       in odds !! 3
-}
  -- will compile just fine, because (evens x) gets desugared into
  -- evens = let _tctemp x = ... in _tctemp

          get_expression _ = internalError "many_cycle . get_expression"
          get_quals :: CDefl -> [CQual]
          get_quals (CLValueSign _ me) = me
          get_quals _ = internalError "many_cycle . get_quals"
          types :: [CType]
          types = map get_type ds

          picks :: (CType,[Pick_func])
          picks = pick_func_list types

          -- these defs are used twice, once inside the tuple ("inner" referred to
          -- above, and the outer ones that live in the same scope as the original
          -- definitions.  They have the same names as the original definitions.
          pick_defs :: [CDefl]
          pick_defs = zipWith create_def ds (snd picks)

          create_def :: CDefl -> Pick_func -> CDefl
          create_def (CLValueSign (CDefT i vs qt _) quals) pick =
              -- trace ("create_def quals " ++ (ppReadable quals)) $
              CLValueSign (CDefT i vs qt [CClause [] -- arguments (including patterns)
                                          [] -- qualifiers ??
                  -- empty values for "arguments" and "qualifiers" are OK because of
                  -- the filter in get_expression
                                          (pick (CVar def_id))])
                              quals -- qualifiers??
          create_def _ _ = internalError("many_cycle . create_def")

          def_id :: Id
          -- this has a chance of causing name collisions.
          def_id = mkId pos1 $ concatFString
                   (List.intersperse fsDollar (map (getIdBase . get_id) ds))

          pos1 :: Position
          pos1 = getPosition d1 -- arbitrarily picking a reasonable position

many_cycle _ _ = internalError "many_cycle on empty list"



-- Prevent polymorphic recursion in self-recursive bindings.
-- Not clear why.
unpoly :: Id -> CExpr -> CExpr
unpoly i (CLam _ _) = internalError "IConv.unpoly: CLam"
unpoly i (CLamT _ _ _) = internalError "IConv.unpoly: CLamT"
unpoly i (Cletrec ds e) = Cletrec (map (unpolyd i) ds) (unpoly i e)
unpoly i (Cletseq ds e) = Cletseq (map (unpolyd i) ds) (unpoly i e)
unpoly i (CSelect _ _) = internalError "IConv.unpoly: CSelect"
unpoly i (CCon _ _) = internalError "IConv.unpoly: CCon"
unpoly i (Ccase _ _ _) = internalError "IConv.unpoly: Ccase"
unpoly i (CStruct _ _ _) = internalError "IConv.unpoly: CStruct"
unpoly i (CStructUpd _ _) = internalError "IConv.unpoly: CStructUpd"
unpoly i (Cwrite _ _ _) = internalError "IConv.unpoly: Cwrite"
unpoly i e@(CAny {}) = e
unpoly i e@(CVar _) = e
-- this is the interesting case
unpoly i (CApply (CTApply f@(CVar i') _) es) | i == i' = CApply f (map (unpoly i) es)
unpoly i (CApply e es) = CApply (unpoly i e) (map (unpoly i) es)
unpoly i (CTaskApplyT e t es) = CTaskApplyT (unpoly i e) t (map (unpoly i) es)
unpoly i (CTaskApply _ _) = internalError "IConv.unpoly: CTaskApply"
unpoly i (CLit _) = internalError "IConv.unpoly: CLit"
unpoly i (CBinOp _ _ _) = internalError "IConv.unpoly: CBinOp"
unpoly i (CHasType _ _) = internalError "IConv.unpoly: CHasType"
unpoly i (Cif _ _ _ _) = internalError "IConv.unpoly: Cif"
unpoly i (CSub _ _ _) = internalError "IConv.unpoly: CSub"
unpoly i (CSub2 _ _ _) = internalError "IConv.unpoly: CSub2"
unpoly i (CSubUpdate _ _ _ _) = internalError "IConv.unpoly: CSubUpdate"
unpoly i (Cmodule _ _) = internalError "IConv.unpoly: Cmodule"
unpoly i (Cinterface pos ii ds) = Cinterface pos ii (map (unpolyd i) ds)
unpoly i (CmoduleVerilog _ _ _ _ _ _ _ _) = internalError "IConv.unpoly: CmoduleVerilog"
unpoly i (CForeignFuncC { }) = internalError "IConv.unpoly: CForeignFuncC"
unpoly i (Cdo _ _) = internalError "IConv.unpoly: Cdo"
unpoly i (Caction _ _) = internalError "IConv.unpoly: Caction"
unpoly i (Crules ps rs) = Crules ps (map (unpolyr i) rs)
unpoly i (COper _) = internalError "IConv.unpoly: COper"
unpoly i (CCon1 _ _ _) = internalError "IConv.unpoly: CCon1"
unpoly i (CSelectTT _ _ _) = internalError "IConv.unpoly: CSelectTT"
unpoly i (CCon0 _ _) = internalError "IConv.unpoly: CCon0"
unpoly i (CConT t ii es) = CConT t ii (map (unpoly i) es)
unpoly i (CStructT t ies) = CStructT t (mapSnd (unpoly i) ies)
unpoly i e@(CSelectT _ _) = e
unpoly i e@(CLitT _ _) = e
unpoly i e@(CAnyT {}) = e
unpoly i (CmoduleVerilogT t e ui clks rsts ses xs v p) = CmoduleVerilogT t (unpoly i e) ui clks rsts (mapSnd (unpoly i) ses) xs v p
unpoly i e@(CForeignFuncCT { }) = e
unpoly i (CTApply e ts) = CTApply (unpoly i e) ts
unpoly i e@(Cattributes ppos) = e
-- Currently exhaustive - uncomment to kill warning
-- unpoly i e = internalError ("IConv.unpoly: fell off! :"++(show e))

unpolyd :: Id -> CDefl -> CDefl
unpolyd i (CLValueSign d qs) = CLValueSign (unpolydd i d) (map (unpolyq i) qs)
unpolyd i (CLValue _ _ _) = internalError "IConv.unpolyd: CLValue"
unpolyd i (CLMatch _ _) = internalError "IConv.unpolyd: CLValue"

unpolyr :: Id -> CRule -> CRule
unpolyr i (CRule ps me qs e) = CRule ps (fmap (unpoly i) me) (map (unpolyq i) qs) (unpoly i e)
unpolyr i (CRuleNest ps me qs rs) = CRuleNest ps (fmap (unpoly i) me) (map (unpolyq i) qs) (map (unpolyr i) rs)

unpolydd :: Id -> CDef -> CDef
unpolydd i (CDef _ _ _) = internalError "IConv.unpolydd: CDef"
unpolydd i (CDefT ii vs t cs) = CDefT ii vs t (map (unpolyc i) cs)

unpolyq :: Id -> CQual -> CQual
unpolyq i (CQGen t p e) = CQGen t p (unpoly i e)
unpolyq i (CQFilter e) = CQFilter (unpoly i e)

unpolyc :: Id -> CClause -> CClause
unpolyc i (CClause ps qs e) = CClause ps (map (unpolyq i) qs) (unpoly i e)

reorderDs :: [CDefl] -> [Id] -> [CDefl]
reorderDs ds is = map get is
--        trace ("order: " ++ (ppReadable is) ++ "\n") $
--        trace ("definitions: " ++ (ppReadable ds) ++ "\n") $
--        trace ("result: " ++ (ppReadable result) ++ "\n") $ result
  where get i = head [ d | d@(CLValueSign (CDefT i' _ _ _) _) <- ds, i == i' ]
--        result = map get is
