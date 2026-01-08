{-# LANGUAGE PatternGuards #-}
module ASyntaxUtil where
import ASyntax

import ErrorUtil(internalError)

import qualified Data.Set as S
import qualified Data.Map as M
import Prim
import PPrint
import IntLit
import SCC(tsort)
import Util(separate)
import Data.List(nub)
import Data.Maybe(mapMaybe, fromMaybe)
import Id(Id)
import Control.Monad(liftM)
import PreIds(idInout_)

-- ---------------

-- IsLiteral is a class to check if A or AX expressions are integer or string literals or not
-- _ is counted as a literal for convenience
-- isLiteralExp is an expression with only literal arguments
isLiteralExp :: AExpr -> Bool
isLiteralExp x = isLiteral x

isLiteral :: AExpr -> Bool
isLiteral (ASInt {}) = True
isLiteral (ASStr {}) = True
isLiteral (ASAny {}) = True
isLiteral (APrim {ae_args = es}) = all isLiteral es
isLiteral _ = False

-- utility function to check if you have a bare constant
isConst :: AExpr -> Bool
isConst (ASInt _ _ (IntLit {})) = True
isConst (ASAny {}) = True
isConst _ = False

isASAny :: AExpr -> Bool
isASAny (ASAny {}) = True
isASAny _          = False

is_aidef :: AIFace -> Bool
is_aidef (AIDef {}) = True
is_aidef _ = False

is_aiaction :: AIFace -> Bool
is_aiaction (AIAction {}) = True
is_aiaction _ = False

isInoutType :: AType -> Bool
isInoutType (ATAbstract i _) = i == idInout_
isInoutType _ = False

-- ---------------

-- aVars is a class that tells you the variables used by a "thing"
class AVars a where
    aVars :: a -> [AId]
    aVars _ = []

instance (AVars a, AVars b) => AVars (a, b) where
    aVars (a, b) = aVars a ++ aVars b

instance AVars AExpr where
    aVars (ASDef _ i) = [i]
    aVars (ASPort _ i) = [i]
    aVars (ASParam _ i) = [i]
    aVars (APrim _ _ _ es) = concatMap aVars es
    aVars (ANoInlineFunCall _ _ _ es) = concatMap aVars es
    aVars (AFunCall _ _ _ _ es) = concatMap aVars es
    aVars (AMethCall _ _ _ es) = concatMap aVars es
    aVars (ATuple _ es) = concatMap aVars es
    aVars (ATupleSel _ e _) = aVars e
--  aVars (ATaskValue ...) = [] -- because the variables are really "used"
-- by the action which sets it
-- same for AMethValue
    aVars _ = []


instance AVars AAction where
    aVars aa = concatMap aVars (aact_args aa)


instance AVars AForeignCall where
    aVars afc = concatMap aVars (afc_args afc)
                        ++ concatMap aVars (afc_resets afc)

instance AVars AIFace where
    aVars (AIDef _ _ _ p d _ asmps) = aVars p ++ aVars d ++ aVars asmps
    aVars (AIAction _ _ p _ rs _) = aVars p ++ aVars rs
    aVars (AIActionValue _ _ p _ rs d _) = aVars p ++ aVars rs ++ aVars d

    -- XXX wire variables?
    aVars _ = []

instance AVars ARule where
    aVars (ARule _ _ _ _ p as asmps _) = aVars p ++ concatMap aVars as ++ concatMap aVars asmps

instance AVars AAssumption where
    aVars (AAssumption p as) = aVars p ++ concatMap aVars as

instance (AVars a) => AVars [a] where
    aVars xs = concatMap aVars xs

instance AVars ADef where
    aVars (ADef _ _ e _) = aVars e

instance AVars AVInst where
    aVars inst = aVars (avi_iargs inst)


-- ---------------

-- find AMethValue uses in an AExpr
aMethValues :: AExpr -> [(AId, AId, AType)]
aMethValues e@(APrim {}) = concatMap aMethValues (ae_args e)
aMethValues e@(AMethCall {}) = concatMap aMethValues (ae_args e)
aMethValues (AMethValue ty obj meth) = [(obj,meth,ty)]
aMethValues (ATuple _ es) = concatMap aMethValues es
aMethValues (ATupleSel _ e _) = aMethValues e
aMethValues e@(ANoInlineFunCall {}) = concatMap aMethValues (ae_args e)
aMethValues e@(AFunCall {}) = concatMap aMethValues (ae_args e)
aMethValues (ATaskValue {}) = []
aMethValues (ASPort {}) = []
aMethValues (ASParam {}) = []
aMethValues (ASDef {}) = []
aMethValues (ASInt {}) = []
aMethValues (ASReal {}) = []
aMethValues (ASStr {}) = []
aMethValues (ASAny {}) = []
aMethValues (ASClock {}) = []
aMethValues (ASReset {}) = []
aMethValues (ASInout {}) = []
aMethValues (AMGate {}) = []

-- find AMethCall uses in an AExpr (ignore references to AV values)
aMethCalls :: AExpr -> [(AId, AId)]
aMethCalls e@(APrim {}) = concatMap aMethCalls (ae_args e)
aMethCalls (AMethCall _ obj meth es) = ((obj,meth) : concatMap aMethCalls es)
aMethCalls (AMethValue _ obj meth) = []
aMethCalls (ATuple _ es) = concatMap aMethCalls es
aMethCalls (ATupleSel _ e _) = aMethCalls e
aMethCalls e@(ANoInlineFunCall {}) = concatMap aMethCalls (ae_args e)
aMethCalls e@(AFunCall {}) = concatMap aMethCalls (ae_args e)
aMethCalls (ATaskValue {}) = []
aMethCalls (ASPort {}) = []
aMethCalls (ASParam {}) = []
aMethCalls (ASDef {}) = []
aMethCalls (ASInt {}) = []
aMethCalls (ASReal {}) = []
aMethCalls (ASStr {}) = []
aMethCalls (ASAny {}) = []
aMethCalls (ASClock {}) = []
aMethCalls (ASReset {}) = []
aMethCalls (ASInout {}) = []
aMethCalls (AMGate {}) = []

-- find ATaskValue uses in an AExpr
aTaskValues :: AExpr -> [(AId, Integer, AType)]
aTaskValues e@(APrim {}) = concatMap aTaskValues (ae_args e)
aTaskValues e@(AMethCall {}) = concatMap aTaskValues (ae_args e)
aTaskValues (AMethValue {}) = []
aTaskValues (ATuple _ es) = concatMap aTaskValues es
aTaskValues (ATupleSel _ e _) = aTaskValues e
aTaskValues e@(ANoInlineFunCall {}) = concatMap aTaskValues (ae_args e)
aTaskValues e@(AFunCall {}) = concatMap aTaskValues (ae_args e)
aTaskValues (ATaskValue ty f_id fun isC cookie) = [(f_id, cookie, ty)]
aTaskValues (ASPort {}) = []
aTaskValues (ASParam {}) = []
aTaskValues (ASDef {}) = []
aTaskValues (ASInt {}) = []
aTaskValues (ASReal {}) = []
aTaskValues (ASStr {}) = []
aTaskValues (ASAny {}) = []
aTaskValues (ASClock {}) = []
aTaskValues (ASReset {}) = []
aTaskValues (ASInout {}) = []
aTaskValues (AMGate {}) = []

-- find calls to foreign functions in an AExpr
exprForeignCalls :: AExpr -> [AExpr]
exprForeignCalls e@(AFunCall {})  =
  if (ae_isC e)
  then e : concatMap exprForeignCalls (ae_args e)
  else (concatMap exprForeignCalls (ae_args e))
exprForeignCalls e@(APrim {})     = concatMap exprForeignCalls (ae_args e)
exprForeignCalls e@(AMethCall {}) = concatMap exprForeignCalls (ae_args e)
exprForeignCalls (ATuple _ es) = concatMap exprForeignCalls es
exprForeignCalls (ATupleSel _ e _) = exprForeignCalls e
exprForeignCalls e@(ANoInlineFunCall {}) =
  concatMap exprForeignCalls (ae_args e)
exprForeignCalls _                  = []

-- find calls to foreign functions in an AAction
actionForeignCalls :: AAction -> [Either AAction AExpr]
actionForeignCalls a@(AFCall {}) =
  if (afcall_isC a)
  then Left a : map Right (concatMap exprForeignCalls (aact_args a))
  else map Right (concatMap exprForeignCalls (aact_args a))
actionForeignCalls a@(ATaskAction {}) =
  if (ataskact_isC a)
  then Left a : map Right (concatMap exprForeignCalls (aact_args a))
  else map Right (concatMap exprForeignCalls (aact_args a))
actionForeignCalls a@(ACall {})  =
  map Right (concatMap exprForeignCalls (aact_args a))

getForeignCallNames :: APackage -> [String]
getForeignCallNames apkg =
  let ffunc_expr_uses    = nub $ findAExprs exprForeignCalls apkg
      ffunc_expr_names   =
        [ i | (AFunCall { ae_funname = i, ae_isC = True }) <- ffunc_expr_uses ]
      ifc_rules          = concatMap aIfaceRules (apkg_interface apkg)
      ffunc_action_uses  = concatMap arule_actions
                                     ((apkg_rules apkg) ++ ifc_rules)
      -- this returns action and expr uses, so take just the fst
      calls              = concatMap actionForeignCalls ffunc_action_uses
      ffunc_actions      = nub $ fst $ separate calls
      ffunc_action_names =
        let getName (AFCall { afcall_fun = i, afcall_isC = True }) = Just i
            getName (ATaskAction { ataskact_fun = i, ataskact_isC = True }) = Just i
            getName _ = Nothing
        in mapMaybe getName ffunc_actions
  in nub (ffunc_expr_names ++ ffunc_action_names)

-- ---------------

-- extract the type and sizes of ASyntax expressions
class ATypeC a where
    aType :: a -> AType
    aSize :: a -> Integer
    aSize e = aSize (aType e)

instance ATypeC AType where
    aSize e =
        case aType e of
        ATBit s -> s
        ATTuple ts -> sum (map aSize ts)
        ATString (Just s) -> 8*s   -- 8 bits per character
        ATAbstract i [n] | i==idInout_ -> n
        ATArray sz t -> sz * (aSize t)
        ATReal -> 64
        t -> internalError ("aSize: " ++ (ppReadable t))
    aType t = t

instance ATypeC AExpr where
    aType e = ae_type e
    aSize e = aSize (ae_type e)

instance ATypeC ADef where
    aType d = adef_type d
    aSize d = aSize $ adef_type d


-- ---------------

class AExprs a where
    mapAExprs :: (AExpr -> AExpr) -> a -> a
    mapMAExprs :: (Monad m) => (AExpr -> m AExpr) -> a -> m a
    findAExprs :: (AExpr -> [b]) -> a -> [b]

instance (AExprs a, AExprs b) => AExprs (a, b) where
    mapAExprs f (a, b) = (mapAExprs f a, mapAExprs f b)
    -- monadic
    mapMAExprs f (a, b) = do a' <- mapMAExprs f a
                             b' <- mapMAExprs f b
                             return (a', b')
    -- find
    findAExprs f (a, b) = findAExprs f a ++ findAExprs f b

instance AExprs AExpr where
    mapAExprs f = f
    -- monadic
    mapMAExprs f = f
    -- find
    findAExprs f = f

instance (AExprs b) => AExprs [b] where
    mapAExprs f l = map (mapAExprs f) l
    -- monadic
    mapMAExprs f l = mapM (mapMAExprs f) l
    -- find
    findAExprs f l = concatMap (findAExprs f) l

instance AExprs AAction where
    mapAExprs f (ACall id mid es) =
        (ACall id mid (mapAExprs f es))
    mapAExprs f (AFCall id fun isC es isA) =
        (AFCall id fun isC (mapAExprs f es) isA)
    mapAExprs f (ATaskAction id fun isC n es tid tty isA) =
        (ATaskAction id fun isC n (mapAExprs f es) tid tty isA)
    -- monadic
    mapMAExprs f (ACall id mid es) =
        do es' <- mapMAExprs f es
           return (ACall id mid es')
    mapMAExprs f (AFCall id fun isC es isA) =
        do es' <- mapMAExprs f es
           return (AFCall id fun isC es' isA)
    mapMAExprs f (ATaskAction id fun isC n es tid tty isA) =
        do es' <- mapMAExprs f es
           return (ATaskAction id fun isC n es' tid tty isA)
    -- find
    findAExprs f (ACall id mid es) = findAExprs f es
    findAExprs f (AFCall id fun isC es isA) = findAExprs f es
    findAExprs f (ATaskAction id fun isC n es tid tty isA) = findAExprs f es

instance AExprs ADef where
    mapAExprs f (ADef id ty e p) = (ADef id ty (mapAExprs f e) p)
    -- monadic
    mapMAExprs f (ADef id ty e p) = do e' <- mapMAExprs f e
                                       return (ADef id ty e' p)
    -- find
    findAExprs f (ADef _ _ e _) = findAExprs f e

instance AExprs AForeignCall where
    -- XXX resets?
    mapAExprs f (AForeignCall id fun es ids resets) =
        (AForeignCall id fun (mapAExprs f es) ids (mapAExprs f resets))
    -- monadic
    mapMAExprs f (AForeignCall id fun es ids resets) =
        do es' <- mapMAExprs f es
           resets' <- mapMAExprs f resets
           return (AForeignCall id fun es' ids resets')
    -- find
    findAExprs f (AForeignCall _ _ es _ resets) =
        findAExprs f es ++ findAExprs f resets

instance AExprs ARule where
    mapAExprs f (ARule rid rps d wp p as asmps splitorig) =
        ARule rid rps d wp (mapAExprs f p) (mapAExprs f as) (mapAExprs f asmps) splitorig
    -- monadic
    mapMAExprs f (ARule rid rps d wp p as asmps splitorig) =
        do p' <- mapMAExprs f p
           as' <- mapMAExprs f as
           asmps' <- mapMAExprs f asmps
           return (ARule rid rps d wp p' as' asmps' splitorig)
    -- find
    findAExprs f (ARule _ _ _ _ p as asmps _) = findAExprs f p ++ findAExprs f as ++ findAExprs f asmps

instance AExprs AAssumption where
   mapAExprs f (AAssumption p as) = AAssumption (mapAExprs f p) (mapAExprs f as)
   mapMAExprs f (AAssumption p as) = do
      p' <- mapMAExprs f p
      as' <- mapMAExprs f as
      return (AAssumption p' as')
   findAExprs f (AAssumption p as) = findAExprs f p ++ findAExprs f as

instance AExprs AIFace where
    mapAExprs f (AIDef mid is wp p def fi asmps) =
        AIDef mid is wp (mapAExprs f p) (mapAExprs f def) fi (mapAExprs f asmps)
    mapAExprs f (AIAction is wp p id rs fi) =
        AIAction is wp (mapAExprs f p) id (mapAExprs f rs) fi
    mapAExprs f (AIActionValue is wp p id rs def fi) =
        AIActionValue is wp (mapAExprs f p) id (mapAExprs f rs) (mapAExprs f def) fi
    mapAExprs f c@(AIClock { }) = c
    mapAExprs f r@(AIReset { }) = r
    mapAExprs f r@(AIInout { }) = r
    -- monadic
    mapMAExprs f (AIDef mid is wp p def fi asmps) =
        do p' <- mapMAExprs f p
           def' <- mapMAExprs f def
           asmps' <- mapMAExprs f asmps
           return (AIDef mid is wp p' def' fi asmps')
    mapMAExprs f (AIAction is wp p id rs fi) =
        do p' <- mapMAExprs f p
           rs' <- mapMAExprs f rs
           return (AIAction is wp p' id rs' fi)
    mapMAExprs f (AIActionValue is wp p id rs def fi) =
        do p' <- mapMAExprs f p
           rs' <- mapMAExprs f rs
           def' <- mapMAExprs f def
           return (AIActionValue is wp p' id rs' def' fi)
    mapMAExprs f c@(AIClock { }) = return c
    mapMAExprs f r@(AIReset { }) = return r
    mapMAExprs f r@(AIInout { }) = return r
    -- find
    findAExprs f (AIDef mid is wp p def fi asmps) =
        findAExprs f p ++ findAExprs f def ++ findAExprs f asmps
    findAExprs f (AIAction is wp p id rs fi) =
        findAExprs f p ++ findAExprs f rs
    findAExprs f (AIActionValue is wp p id rs def fi) =
        findAExprs f p ++ findAExprs f rs ++ findAExprs f def
    findAExprs f c@(AIClock { }) = []
    findAExprs f r@(AIReset { }) = []
    findAExprs f r@(AIInout { }) = []

instance AExprs AVInst where
    mapAExprs f inst = inst { avi_iargs = (mapAExprs f (avi_iargs inst)) }
    -- monadic
    mapMAExprs f inst = do iargs' <- mapMAExprs f (avi_iargs inst)
                           return (inst { avi_iargs = iargs' })
    -- find
    findAExprs f inst = findAExprs f (avi_iargs inst)

instance AExprs ASPackage where
    mapAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                aspkg_values = defs,
                                aspkg_inout_values = iodefs,
                                aspkg_foreign_calls = fs })
        = pkg { aspkg_state_instances = (mapAExprs f vs),
                aspkg_values = (mapAExprs f defs),
                aspkg_inout_values = (mapAExprs f iodefs),
                aspkg_foreign_calls = (mapAExprs f fs) }
    -- monadic
    mapMAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                  aspkg_values = defs,
                                  aspkg_inout_values = iodefs,
                                  aspkg_foreign_calls = fs })
        = do vs' <- mapMAExprs f vs
             defs' <- mapMAExprs f defs
             iodefs' <- mapMAExprs f iodefs
             fs' <- mapMAExprs f fs
             return (pkg { aspkg_state_instances = vs',
                           aspkg_values = defs',
                           aspkg_inout_values = iodefs',
                           aspkg_foreign_calls = fs' })
    -- find
    findAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                aspkg_values = defs,
                                aspkg_inout_values = iodefs,
                                aspkg_foreign_calls = fs })
        = findAExprs f vs ++ findAExprs f defs ++
          findAExprs f iodefs ++ findAExprs f fs

instance AExprs APackage where
    mapAExprs f pack = pack {
        apkg_interface = mapAExprs f (apkg_interface pack),
        apkg_rules = mapAExprs f (apkg_rules pack),
        apkg_state_instances = mapAExprs f (apkg_state_instances pack),
        apkg_local_defs = mapAExprs f (apkg_local_defs pack) }
    -- monadic
    mapMAExprs f pack@(APackage { apkg_interface = ifc,
                                  apkg_rules = rs,
                                  apkg_state_instances = insts,
                                  apkg_local_defs = defs })
        = do ifc' <- mapMAExprs f ifc
             rs' <- mapMAExprs f rs
             insts' <- mapMAExprs f insts
             defs' <- mapMAExprs f defs
             return (pack { apkg_interface = ifc',
                            apkg_rules = rs',
                            apkg_state_instances = insts',
                            apkg_local_defs = defs' })
    -- find
    findAExprs f pack =
        findAExprs f (apkg_interface pack) ++
        findAExprs f (apkg_rules pack) ++
        findAExprs f (apkg_state_instances pack) ++
        findAExprs f (apkg_local_defs pack)


-- ---------------

-- substitute into b using a map from AIds to AExprs
-- defined in terms of mapAExprs

type EMap a = M.Map AId a

aSubst :: (AExprs a) => EMap AExpr -> a -> a
aSubst m = mapAExprs xsub
  where xsub :: AExpr -> AExpr
        xsub x@(ASPort _ i) = M.findWithDefault x i m
        xsub x@(ASParam _ i) = M.findWithDefault x i m
        xsub x@(ASDef _ i) = M.findWithDefault x i m
        xsub (APrim aid t p es) = APrim aid t p (aSubst m es)
        xsub (AMethCall t i meth es) = AMethCall t i meth (aSubst m es)
        xsub (ATuple t es) = ATuple t (aSubst m es)
        xsub (ATupleSel t e n) = ATupleSel t (aSubst m e) n
        xsub (ANoInlineFunCall t i f es) = ANoInlineFunCall t i f (aSubst m es)
        xsub (AFunCall t i f isC es) = AFunCall t i f isC (aSubst m es)
        xsub (ASAny t me) = ASAny t (fmap (aSubst m) me)
        xsub x = x


-- ---------------
-- recursive expression mapping

exprMap :: (AExpr -> Maybe AExpr) -> AExpr -> AExpr
exprMap f e@(ASAny t (Just v)) =
  let e' = ASAny t (Just ((exprMap f) v))
  in fromMaybe e' (f e)
exprMap f e@(APrim i t o args) =
  let e' = APrim i t o (map (exprMap f) args)
  in fromMaybe e' (f e)
exprMap f e@(AMethCall t i m args) =
  let e' = AMethCall t i m (map (exprMap f) args)
  in fromMaybe e' (f e)
exprMap f e@(ATuple t args) =
  let e' = ATuple t (map (exprMap f) args)
  in fromMaybe e' (f e)
exprMap f e@(ATupleSel t expr n) =
  let e' = ATupleSel t (exprMap f expr) n
  in fromMaybe e' (f e)
exprMap f e@(ANoInlineFunCall t i fun args) =
  let e' = ANoInlineFunCall t i fun (map (exprMap f) args)
  in fromMaybe e' (f e)
exprMap f e@(AFunCall t i fun isC args) =
  let e' = AFunCall t i fun isC (map (exprMap f) args)
  in fromMaybe e' (f e)
exprMap f e = fromMaybe e (f e)

exprMapM :: (Monad m) => (AExpr -> m (Maybe AExpr)) -> AExpr -> m AExpr
exprMapM f e@(ASAny t (Just v)) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do v' <- (exprMapM f) v
                  return $ ASAny t (Just v')
exprMapM f e@(APrim i t o args) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do args' <- mapM (exprMapM f) args
                  return $ APrim i t o args'
exprMapM f e@(AMethCall t i m args) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do args' <- mapM (exprMapM f) args
                  return $ AMethCall t i m args'
exprMapM f e@(ATuple t elems) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do elems' <- mapM (exprMapM f) elems
                  return $ ATuple t elems'
exprMapM f e@(ATupleSel t expr n) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do expr' <- exprMapM f expr
                  return $ ATupleSel t expr' n
exprMapM f e@(ANoInlineFunCall t i fun args) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do args' <- mapM (exprMapM f) args
                  return $ ANoInlineFunCall t i fun args'
exprMapM f e@(AFunCall t i fun isC args) = do
  me <- f e
  case me of
    Just e' -> return e'
    Nothing -> do args' <- mapM (exprMapM f) args
                  return $ AFunCall t i fun isC args'
exprMapM f e = do
  me <- f e
  return $ fromMaybe e me

-- ---------------
-- folding over an expression

exprFold :: (AExpr -> a -> a) -> a -> AExpr -> a
exprFold f v e@(APrim i t o args) =
  let v' = foldr (flip (exprFold f)) v args
  in f e v'
exprFold f v e@(AMethCall t i m args) =
  let v' = foldr (flip (exprFold f)) v args
  in f e v'
exprFold f v e@(ATuple t elems) =
  let v' = foldr (flip (exprFold f)) v elems
  in f e v'
exprFold f v e@(ATupleSel t expr n) =
  let v' = exprFold f v expr
  in f e v'
exprFold f v e@(ANoInlineFunCall t i fun args) =
  let v' = foldr (flip (exprFold f)) v args
  in f e v'
exprFold f v e@(AFunCall t i fun isC args) =
  let v' = foldr (flip (exprFold f)) v args
  in f e v'
exprFold f v e = f e v

-- ---------------

-- action to action transform instead of expression to expression
class AActions a where
    mapAActions :: (AAction -> AAction) -> a -> a

instance (AActions a, AActions b) => AActions (a, b) where
    mapAActions f (a, b) = (mapAActions f a, mapAActions f b)

instance (AActions b) => AActions [b] where
    mapAActions f l = map (mapAActions f) l

instance AActions AAction where
    mapAActions f = f

instance AActions ARule where
    mapAActions f (ARule rid rps d wp p as asmps splitorig) = ARule rid rps d wp p (mapAActions f as) (mapAActions f asmps) splitorig

instance AActions AAssumption where
    mapAActions f asmp@(AAssumption { assump_actions = as }) = asmp { assump_actions = mapAActions f as }

instance AActions AIFace where
    mapAActions f d@(AIDef mid is wp p def fi asmps) = d { aif_assumps = mapAActions f asmps }
    mapAActions f (AIAction is wp p id rs fi) = AIAction is wp p id (mapAActions f rs) fi
    mapAActions f (AIActionValue is wp p id rs def fi) = AIActionValue is wp p id (mapAActions f rs) def fi
    mapAActions f c@(AIClock { }) = c
    mapAActions f r@(AIReset { }) = r
    mapAActions f r@(AIInout { }) = r

instance AActions APackage where
    mapAActions f pack = pack {
        apkg_interface = mapAActions f (apkg_interface pack),
        apkg_rules     = mapAActions f (apkg_rules pack)
    }


-- ---------------

-- rule to rule transform instead of expression to expression
class ARules a where
    mapARules :: (ARule -> ARule) -> a -> a

instance (ARules a, ARules b) => ARules (a, b) where
    mapARules f (a, b) = (mapARules f a, mapARules f b)

instance (ARules b) => ARules [b] where
    mapARules f l = map (mapARules f) l

instance ARules ARule where
    mapARules f = f

instance ARules AIFace where
    mapARules f d@(AIDef {}) = d
    mapARules f (AIAction is wp p id rs fi) = AIAction is wp p id (mapARules f rs) fi
    mapARules f (AIActionValue is wp p id rs def fi) = AIActionValue is wp p id (mapARules f rs) def fi
    mapARules f c@(AIClock { }) = c
    mapARules f r@(AIReset { }) = r
    mapARules f r@(AIInout { }) = r

instance ARules APackage where
    mapARules f pack = pack {
        apkg_interface = mapARules f (apkg_interface pack),
        apkg_rules     = mapARules f (apkg_rules pack)
    }


-- ---------------

-- lift an AId mapping function to an AExpr mapping function
-- XXX why does this not map over method Ids, for instance?
aIdFnToAExprFn :: (AId -> AId) -> (AExpr -> AExpr)
aIdFnToAExprFn fn (APrim aid ty op args) =
    APrim (fn aid) ty op (mapAExprs (aIdFnToAExprFn fn) args)
aIdFnToAExprFn fn (AMethCall ty aid mid args) =
    AMethCall ty (fn aid) mid (mapAExprs (aIdFnToAExprFn fn) args)
aIdFnToAExprFn fn (AMethValue ty aid mid) =
    AMethValue ty (fn aid) mid
aIdFnToAExprFn fn (ATuple ty exprs) =
    ATuple ty (mapAExprs (aIdFnToAExprFn fn) exprs)
aIdFnToAExprFn fn (ATupleSel ty expr n) =
    ATupleSel ty (aIdFnToAExprFn fn expr) n
aIdFnToAExprFn fn (ANoInlineFunCall ty aid fun args) =
    ANoInlineFunCall ty (fn aid) fun (mapAExprs (aIdFnToAExprFn fn) args)
aIdFnToAExprFn fn (AFunCall ty aid fun isC args) =
    AFunCall ty (fn aid) fun isC (mapAExprs (aIdFnToAExprFn fn) args)
aIdFnToAExprFn fn (ATaskValue ty aid fun isC cookie) =
    ATaskValue ty (fn aid) fun isC cookie
aIdFnToAExprFn fn (ASPort ty aid) = ASPort ty (fn aid)
aIdFnToAExprFn fn (ASParam ty aid) = ASParam ty (fn aid)
aIdFnToAExprFn fn (ASDef ty aid) = ASDef ty (fn aid)
aIdFnToAExprFn fn (ASInt aid ty v) = ASInt (fn aid) ty v
aIdFnToAExprFn fn (ASReal aid ty v) = ASReal (fn aid) ty v
aIdFnToAExprFn fn (ASStr aid ty s) = ASStr (fn aid) ty s
aIdFnToAExprFn fn (ASAny ty (Just e)) = ASAny ty (Just ((aIdFnToAExprFn fn) e))
aIdFnToAExprFn fn (AMGate ty aid cid) = AMGate ty (fn aid) cid
aIdFnToAExprFn _ expr = expr -- identity function for everything without AIds

-- lift an AId mapping function to an AAction mapping function
aIdFnToAActionFn :: (AId -> AId) -> (AAction -> AAction)
aIdFnToAActionFn fn (ACall aid mid args) =
    ACall (fn aid) mid (mapAExprs (aIdFnToAExprFn fn) args)
aIdFnToAActionFn fn (AFCall aid fun isC args isA) =
    AFCall (fn aid) fun isC (mapAExprs (aIdFnToAExprFn fn) args) isA
aIdFnToAActionFn fn (ATaskAction aid fun isC cookie args temp ty isA) =
    let args' = mapAExprs (aIdFnToAExprFn fn) args
        temp' = (liftM fn) temp
    in ATaskAction (fn aid) fun isC cookie args' temp' ty isA

-- ---------------

-- topological sorting of ADefs
tsortADefs :: [ADef] -> [ADef]
tsortADefs ds =
--    trace ("tsortADefs enter " ++ show (length ds)) $
    -- ds_ids are the AIds from the input ADefs
    -- s is a OrdSet of AId from the input ADefs
    let
        ds_ids = (map adef_objid ds)
        s = S.fromList ds_ids
    -- g is a list of (AId, [AIds used by that ADef which are in 's'
    --   drop all other AIds (mostly AVars)
--        g = [(i, filter (`S.member` s) (aVars e)) | ADef i _ e <- ds ]
        g = zip ds_ids (map ((filter (`S.member` s)) . aVars . adef_expr) ds)
    -- tsort returns Left if there is a loop, Right if sorted
    in  case tsort g of
        Left is -> internalError ("tsortADefs: cyclic " ++ ppReadable is ++ ppReadable ds)
        Right is -> --trace ("tsortADefs exit " ++ show (length is)) $
    -- m is OrdMap of (AId of ADef, ADef) from input ADefs
            let m = M.fromList (zip ds_ids ds)
    -- get i is OrdMap lookup giving ADef in m from AId
                get i = case M.lookup i m of Just d -> d; Nothing -> internalError "tsortADefs: get"
    -- return ADefs in tsort-ed order removing AIds.
            in  map get is

-- ---------------

aBoolVar :: Id -> AExpr
aBoolVar i = ASDef aTBool i

aBoolPort :: Id -> AExpr
aBoolPort i = ASPort aTBool i

aNot :: AExpr -> AExpr
aNot = aNotLabel defaultAId

aAnd :: AExpr -> AExpr -> AExpr
aAnd = aAndLabel defaultAId

aOr :: AExpr -> AExpr -> AExpr
aOr = aOrLabel defaultAId

aNotLabel :: AId -> AExpr -> AExpr
aNotLabel _ (APrim aid t PrimBNot [e]) | t == aTBool = e
aNotLabel _ x                          | isTrue x    = aFalse
aNotLabel _ x                          | isFalse x   = aTrue
aNotLabel aid x                                      = APrim aid aTBool PrimBNot [x]

aAndLabel :: AId -> AExpr -> AExpr -> AExpr
aAndLabel _ x y                         | isTrue x                   = y
aAndLabel _ x y                         | isTrue y                   = x
aAndLabel _ x y                         | isFalse y || isFalse x     = aFalse
aAndLabel _ x y                         | x == y                     = x
aAndLabel aid (APrim _ t1 PrimBAnd es) (APrim _ t2 PrimBAnd fs)
                                        | t1 == aTBool, t2 == aTBool = APrim aid t1 PrimBAnd (es++fs)
aAndLabel aid x (APrim _ t PrimBAnd es) | t == aTBool                = APrim aid t PrimBAnd (x:es)
aAndLabel aid (APrim _ t PrimBAnd es) x | t == aTBool                = APrim aid t PrimBAnd (x:es)
aAndLabel aid x y                                                    = APrim aid aTBool PrimBAnd [x, y]

aAnds :: [AExpr] -> AExpr
aAnds = aAndsLabel defaultAId

aAndsLabel :: AId -> [AExpr] -> AExpr
aAndsLabel _ [] = internalError "ASyntaxUtil::aAnds null list"
aAndsLabel _ [e] = e
aAndsLabel aid es = if any isFalse es then aFalse else aAnds' (nub (filter (not . isTrue) es))
  where aAnds' []  = aTrue
        aAnds' [e] = e
        aAnds' es  = APrim aid aTBool PrimBAnd es


aOrLabel :: AId -> AExpr -> AExpr -> AExpr
aOrLabel _ x y                        | isFalse x                  = x
aOrLabel _ x y                        | isFalse y                  = y
aOrLabel _  x y                       | isTrue y || isTrue x       = aTrue
aOrLabel _  x y                       | x == y                     = x
aOrLabel aid (APrim _ t1 PrimBOr es) (APrim _ t2 PrimBOr fs)
                                      | t1 == aTBool, t2 == aTBool = APrim aid t1 PrimBOr (es++fs)
aOrLabel aid x (APrim _ t PrimBOr es) | t == aTBool                = APrim aid t  PrimBOr (x:es)
aOrLabel aid (APrim _ t PrimBOr es) x | t == aTBool                = APrim aid t  PrimBOr (x:es)
aOrLabel aid x y                                                   = APrim aid aTBool PrimBOr [x, y]


aOrs :: [AExpr] -> AExpr
aOrs = aOrsLabel defaultAId

aOrsLabel :: AId -> [AExpr] -> AExpr
aOrsLabel _ [] = internalError "ASyntaxUtil::aOrs null list"
aOrsLabel _ [e] = e
aOrsLabel aid es = if any isTrue es then aTrue else aOrs' (nub (filter (not . isFalse) es))
  where aOrs' []  = aFalse
        aOrs' [e] = e
        aOrs' es  = APrim aid aTBool PrimBOr es
