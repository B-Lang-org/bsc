module Parser.Classic.Warnings(classicWarnings) where

import Control.Monad(when)
import Control.Monad.Reader(ReaderT, runReaderT, ask, local)
import Control.Monad.Writer(Writer, runWriter, tell, listen, censor)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Set(Set, (\\))

import CFreeVars
import CSyntax
import CSyntaxUtil
import Error
import Id
import Position
import Util(concatMapM, fromJustOrErr)

-- ReaderT (bound variables) $ Writer (used variables)
type ClassicWarnM = ReaderT (Set Id) (Writer (Set Id))

classicWarnings :: CPackage -> [WMsg]
classicWarnings (CPackage _ _ _ _ _ ds _) = concatMap getWarnings ds
  where getWarnings = fst . runWriter . (flip runReaderT $ topBound) . classicWarnDefn
        topBound = S.fromList $ concatMap getBound ds
        getBound (Ctype {}) = []
        getBound (Cdata {}) = []
        getBound (Cstruct {}) = []
        -- Ignoring shadowing of class methods (for now at least).
        getBound (Cclass {}) = []
        getBound (Cinstance {}) = []
        getBound (CValue i _) = [i]
        getBound (CValueSign (CDef i _ _)) = [i]
        getBound (CValueSign (CDefT i _ _ _)) = [i]
        getBound (Cforeign i _ _ _ _) = [i]
        getBound (Cprimitive i _) = [i]
        getBound (CprimType {}) = []
        getBound (CPragma {}) = []
        -- Ignore shadowing of imported names.
        getBound (CIinstance {}) = []
        getBound (CItype {}) = []
        getBound (CIclass {}) = []
        getBound (CIValueSign {}) = []

classicWarnDefn :: CDefn -> ClassicWarnM [WMsg]
classicWarnDefn (Ctype {}) = return []
classicWarnDefn (Cdata {}) = return []
classicWarnDefn (Cstruct {}) = return []
-- Could look at default method definitions, but this seems like overkill.
classicWarnDefn (Cclass {}) = return []
-- Instances could also be overkill, but they can get complicated.
classicWarnDefn (Cinstance _ ds) = concatMapM classicWarnDefl ds
classicWarnDefn (CValue _ cs) = concatMapM classicWarnClause cs
classicWarnDefn (CValueSign d) = classicWarnDef d
classicWarnDefn (Cforeign {}) = return []
classicWarnDefn (Cprimitive {}) = return []
classicWarnDefn (CprimType {}) = return []
classicWarnDefn (CPragma {}) = return []
-- Don't warn about imported definitions
classicWarnDefn (CIinstance {}) = return []
classicWarnDefn (CItype {}) = return []
classicWarnDefn (CIclass {}) = return []
classicWarnDefn (CIValueSign {}) = return []

useId :: Id -> ClassicWarnM ()
useId i = tell $ S.singleton i

withBindings :: Set Id -> ClassicWarnM [WMsg] -> ClassicWarnM [WMsg]
withBindings bindings m = do
  bound <- ask
  let shadowed = bound `S.intersection` bindings
      bindPosMap = M.fromSet getPosition bindings
      bindingPosition i = fromJustOrErr ("withBindings not found: " ++ show i) $ M.lookup i bindPosMap
      shadow_ws = [ (bindingPosition i, WShadowDecl (getIdString i) (getPosition i))
                  | i <- S.toList shadowed
                  ]
  local (const $ bindings `S.union` bound) $ censor (\\ bindings) $ do
      (ws, used) <- listen m
      let unused_ws = [ (getPosition i, WUnusedDef (getIdString i))
                      | i <- S.toList (bindings \\ used), take 1 (getIdString i) /= "_"
                      ]
      return $ shadow_ws ++ ws ++ unused_ws

-- Quals add names in sequence, so we need to handle them only-by-one.
withQuals :: [CQual] -> ClassicWarnM [WMsg] -> ClassicWarnM [WMsg]
withQuals [] m = m
withQuals (CQFilter e : qs) m = do
  ws1 <- classicWarnExpr e
  ws2 <- withQuals qs m
  return $ ws1 ++ ws2
withQuals (CQGen _ p e : qs) m = do
  ws1 <- classicWarnExpr e
  ws2 <- withBindings (getPV p) $ withQuals qs m
  return $ ws1 ++ ws2

-- Recursion is handled outside of classicWarnDefl, based on context.
classicWarnDefl :: CDefl -> ClassicWarnM [WMsg]
classicWarnDefl (CLValueSign d qs) =
  withQuals qs $ classicWarnDef d
classicWarnDefl (CLValue i cs qs) =
  withQuals qs $ concatMapM classicWarnClause cs
classicWarnDefl (CLMatch p e) =
  -- CLMatch binds variables based on the value of e, so they aren't
  -- in scope when checking the expression.
  classicWarnExpr e

-- Recursion is handled outside of classicWarnDef, based on context.
classicWarnDef :: CDef -> ClassicWarnM [WMsg]
classicWarnDef (CDef i _ cs) = concatMapM classicWarnClause cs
classicWarnDef (CDefT i _ _ cs) = concatMapM classicWarnClause cs

classicWarnClause :: CClause -> ClassicWarnM [WMsg]
classicWarnClause (CClause ps qs e) =
  withBindings (S.unions $ map getPV ps) $
    withQuals qs $ classicWarnExpr e

classicWarnArm :: CCaseArm -> ClassicWarnM [WMsg]
classicWarnArm arm =
  withBindings (getPV $ cca_pattern arm) $
    withQuals (cca_filters arm) $
     classicWarnExpr $ cca_consequent arm

classicWarnExpr :: CExpr -> ClassicWarnM [WMsg]
classicWarnExpr (CLam (Right i) e) = withBindings (S.singleton i) $ classicWarnExpr e
classicWarnExpr (CLam (Left  _) e) = classicWarnExpr e
classicWarnExpr (CLamT (Right i) _ e) = withBindings (S.singleton i) $ classicWarnExpr e
classicWarnExpr (CLamT (Left _) _ e) = classicWarnExpr e
classicWarnExpr (Cletseq [] e) = classicWarnExpr e
classicWarnExpr (Cletseq (d:ds) e) = do
  ws1 <- classicWarnDefl d
  ws2 <- withBindings (S.fromList $ getLDefs d) $ classicWarnExpr (Cletseq ds e)
  return $ ws1 ++ ws2
classicWarnExpr (Cletrec ds e) =
  withBindings (S.fromList $ concatMap getLDefs ds) $ do
    ws1 <- concatMapM classicWarnDefl ds
    ws2 <- classicWarnExpr e
    return $ ws1 ++ ws2
-- _i is a field selector, not a variable
classicWarnExpr (CSelect e _i) = classicWarnExpr e
classicWarnExpr (CCon _c es) = concatMapM classicWarnExpr es
classicWarnExpr (Ccase _ e as) = do
  ws1 <- classicWarnExpr e
  ws2 <- concatMapM classicWarnArm as
  return $ ws1 ++ ws2
classicWarnExpr (CStruct _ _ ies) = concatMapM (classicWarnExpr . snd) ies
classicWarnExpr (CStructUpd e ies) = concatMapM classicWarnExpr (e : map snd ies)
classicWarnExpr (Cwrite _ lhs rhs) = do
  ws1 <- classicWarnExpr lhs
  ws2 <- classicWarnExpr rhs
  return $ ws1 ++ ws2
classicWarnExpr (CAny _ _) = return []
classicWarnExpr (CVar i) = do useId i; return []
classicWarnExpr (CApply f es) = concatMapM classicWarnExpr (f:es)
classicWarnExpr (CTaskApply f es) = concatMapM classicWarnExpr (f:es)
classicWarnExpr (CTaskApplyT f _ es) = concatMapM classicWarnExpr (f:es)
classicWarnExpr (CLit _) = return []
classicWarnExpr (CBinOp l i r) = do
  useId i
  ws1 <- classicWarnExpr l
  ws2 <- classicWarnExpr r
  return $ ws1 ++ ws2
classicWarnExpr (CHasType e _) = classicWarnExpr e
classicWarnExpr (Cif _ c t e) = concatMapM classicWarnExpr [c,t,e]
classicWarnExpr (CSub _ x a) = do
  ws1 <- classicWarnExpr x
  ws2 <- classicWarnExpr a
  return $ ws1 ++ ws2
classicWarnExpr (CSub2 x a b) = concatMapM classicWarnExpr [x, a, b]
classicWarnExpr (CSubUpdate _ x (a, b) y) = concatMapM classicWarnExpr [x, a, b, y]
classicWarnExpr (Cmodule pos ms) = classicWarnMStmts pos ms
classicWarnExpr (Cinterface _ _ ds) = concatMapM classicWarnDefl ds
classicWarnExpr (CmoduleVerilog n _ _ _ vargs _ _ _) = concatMapM classicWarnExpr (n : map snd vargs)
classicWarnExpr (CForeignFuncC _ _) = return []
classicWarnExpr (Cdo _ stmts) = classicWarnStmts Nothing stmts
classicWarnExpr (Caction _ stmts) = classicWarnStmts Nothing stmts
classicWarnExpr (Crules _ rs) = concatMapM classicWarnRule rs
classicWarnExpr (COper ops) = concatMapM classicWarnOp ops
classicWarnExpr (CCon1 _ _ e) = classicWarnExpr e
classicWarnExpr (CSelectTT _ e _) = classicWarnExpr e
classicWarnExpr (CCon0 _ _) = return []
classicWarnExpr (CConT _ _ es) = concatMapM classicWarnExpr es
classicWarnExpr (CStructT _ ies) = concatMapM (classicWarnExpr . snd) ies
classicWarnExpr (CSelectT _ _) = return []
classicWarnExpr (CLitT _ _) = return []
classicWarnExpr (CAnyT _ _ _) = return []
classicWarnExpr (CmoduleVerilogT _ n _ _ _ vargs _ _ _) = concatMapM classicWarnExpr (n : map snd vargs)
classicWarnExpr (CForeignFuncCT _ _) = return []
classicWarnExpr (CTApply e _) = classicWarnExpr e
classicWarnExpr (Cattributes _) = return []

classicWarnMStmts :: Position -> [CMStmt] -> ClassicWarnM [WMsg]
classicWarnMStmts pos = classicWarnStmts (Just pos) . map toStmt
  where toStmt (CMStmt s) = s
        toStmt (CMrules e) = CSExpr Nothing e
        toStmt (CMinterface e) = CSExpr Nothing e
        toStmt (CMTupleInterface pos es) = CSExpr Nothing (mkTuple pos es)

rebuildBody :: Maybe Position -> [CStmt] -> CExpr
-- Cdo False might not be right, but we ignore this argument of Cdo anyway.
rebuildBody Nothing stmts = Cdo False stmts
rebuildBody (Just modPos) stmts = Cmodule modPos $ map CMStmt stmts

-- The Maybe Position is Just pos for statements that came from a module context.
classicWarnStmts :: Maybe Position -> [CStmt] -> ClassicWarnM [WMsg]
classicWarnStmts _ [] = return []
classicWarnStmts modPos (CSBindT p _ _ _ e : stmts) = do
  ws1 <- classicWarnExpr e
  let bvs = getPV p
  ws2 <- withBindings bvs $ do
           -- In module context, monadically bound names are always "used".
           -- (via their side effect on instance names)
           when (isJust modPos) (mapM_ useId $ S.toList bvs)
           classicWarnStmts modPos stmts
  return $ ws1 ++ ws2
classicWarnStmts modPos (CSBind p _ _ e : stmts) = do
  ws1 <- classicWarnExpr e
  let bvs = getPV p
  ws2 <- withBindings bvs $ do
           -- In module context, monadically bound names are always "used".
           -- (via their side effect on instance names)
           when (isJust modPos) (mapM_ useId $ S.toList bvs)
           classicWarnStmts modPos stmts
  return $ ws1 ++ ws2
classicWarnStmts modPos (CSletseq ds : stmts)
  = classicWarnExpr (Cletseq ds $ rebuildBody modPos stmts)
classicWarnStmts modPos (CSletrec ds : stmts)
  = classicWarnExpr (Cletrec ds $ rebuildBody modPos stmts)
classicWarnStmts modPos (CSExpr _ e  : stmts) = do
  ws1 <- classicWarnExpr e
  ws2 <- classicWarnStmts modPos stmts
  return $ ws1 ++ ws2

classicWarnRule :: CRule -> ClassicWarnM [WMsg]
classicWarnRule (CRule _ mname qs e) = do
  ws1 <- maybe (return []) classicWarnExpr $ mname
  ws2 <- withQuals qs $ classicWarnExpr e
  return $ ws1 ++ ws2
classicWarnRule (CRuleNest _ mname qs rs) = do
  ws1 <- maybe (return []) classicWarnExpr $ mname
  ws2 <- withQuals qs $ concatMapM classicWarnRule rs
  return $ ws1 ++ ws2

classicWarnOp :: COp -> ClassicWarnM [WMsg]
classicWarnOp (CRand e) = classicWarnExpr e
classicWarnOp (CRator _ i) = do useId i; return []
