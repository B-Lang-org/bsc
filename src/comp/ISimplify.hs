module ISimplify(iSimplify) where

import Data.List((\\))
import qualified Data.Map as M
import qualified Data.Set as S
import Util(fromJustOrErr)
import PPrint
import IntLit
import ErrorUtil
import Id
import ISyntax
import ISyntaxSubst(eSubst, etSubst)
import Prim
import ISyntaxUtil(aitBit, isTrue, isFalse, isitActionValue_, isitActionValue, iDefsMap)
import ISyntaxXRef(mapIExprPosition)
import Eval
--import Debug.Trace
--import Util(traces)
--import Position

--
-- TODO
--  Useful transformations (from looking at .bo)
--   * let x = (a,b) in ... fst x ... snd x ...  -->  ... a ... b ...
--     note that the tuple transformation is important to inline dictionaries (I think)
--   * PrimConcat 0 n n _ x  -->  x
--   * let d = Literal-Bits n in ... .fromInteger d NNN  -->   NNN

iSimplify :: (NFData a) => IPackage a -> IPackage a
iSimplify (IPackage pi lps ps ds) =
    IPackage pi lps ps ({-iSimpDefs-} (iSimpDefs (iSimpDefs ds)))        -- XXX

iSimpDefs :: NFData a => [IDef a] -> [IDef a]
iSimpDefs ds = fixUpDefs $ iDefsMap (iSimp True) ds

iSimp :: (NFData a) => Bool -> IExpr a -> IExpr a
iSimp n (ILam i t e) = ILam i t (iSimp n e)
iSimp n (IAps e ts as) = iSimpAp' n (iSimp n (expDef e)) ts (map (iSimp n) as)
iSimp _ e@(IVar _) = e
iSimp n (ILAM i k e) = ILAM i k (iSimp n e)
iSimp _ e@(ICon _ _) = e
iSimp _ e = internalError ("iSimp: " ++ ppReadable e)

expDef :: IExpr a -> IExpr a
expDef (ICon _ (ICDef _ e)) | isHarmless e = e
expDef e = e

iSimpAp' :: NFData a => Bool -> IExpr a -> [IType] -> [IExpr a] -> IExpr a
iSimpAp' b f ts es = mapIExprPosition True (f, iSimpAp b f ts es)

iSimpAp :: (NFData a) => Bool -> IExpr a -> [IType] -> [IExpr a] -> IExpr a
iSimpAp n (ILAM i _ e) (t:ts) as = iSimpAp n (etSubst i t e) ts as
iSimpAp n (ILam i _ e) [] (a:as)
    | not (isKeepId i) && (isTriv a || countOcc i e <= 1) =
        let e' = eSubst i a e
        in iSimpAp n e' [] as
iSimpAp _ (ICon _ (ICPrim _ prim)) ts es | m /= Nothing = r
  where m = doPrim prim ts es
        r = fromJustOrErr "iSimpAp ICPrim Nothing" m
iSimpAp n f@(ICon _ (ICSel { selNo = k })) ts
        es@(def : as) | n && m /= Nothing = {-trace (ppReadable (IAps f ts es, e'))-} e'
  where m = selectTuple (fromInteger k) def
        e = fromJustOrErr "iSimpAp ICSel Nothing" m
        e' = iSimpAp n e [] as
iSimpAp n e [] [] = e -- iSimp has already been called
iSimpAp n f ts es = IAps f ts es

selectTuple :: (NFData a) => Int -> IExpr a -> Maybe (IExpr a)
selectTuple k (ICon di (ICDef { iConDef = def@(IAps (ICon _ (ICTuple { })) _ ms) })) | di `notElem` dVars e = Just e
  where e = ms !! k
selectTuple k (IAps (ICon iii (ICDef { iConDef = body })) ts []) =
        -- trace ("getTuple " ++ ppReadable (iii,body)) $
        case iSimpAp False body ts [] of
        IAps (ICon _ (ICTuple { })) _ ms -> Just $ ms !! k
        _ -> Nothing
selectTuple _ _ = Nothing

-- XXX should we do more PrimOps here?
doPrim :: PrimOp -> [IType] -> [IExpr a] -> Maybe (IExpr a)
doPrim PrimIntegerToBit [t@(ITNum s)] [ICon i l@(ICInt { iVal = v })] | ilValue v >= 0 &&
                                                                        s >=0 &&
                                                                        ilValue v < 2^s = Just $ ICon i (l { iConType = aitBit t })
doPrim PrimOrd          [t,s] [IAps (ICon _ (ICPrim _ PrimChr)) [s',t'] [e]] | s == s' && t == t' = Just e
doPrim PrimIf _ [c, t, e] | isTrue  c = Just t
                          | isFalse c = Just e
doPrim _ _ _ = Nothing

{-
data Occ = None | One | Many
  deriving(Eq)
-}


countOcc :: Id -> IExpr a -> Int
countOcc i e = countOcc' i e 0

countOcc' :: Id -> IExpr a -> Int -> Int
countOcc' _ _ occ | occ > 1   = occ
countOcc' i (ILam i' _ e) occ = if i == i' then occ else countOcc' i e occ
countOcc' i (IAps f _ es) occ = foldr (countOcc' i) (countOcc' i f occ) es
countOcc' i (IVar i') occ     = if i == i' then occ + 1 else occ
countOcc' i (ILAM _ _ e) occ  = countOcc' i e occ
countOcc' _ _ occ             = occ

{-
size :: IExpr -> Int
size (ILam _ _ e) = size e
size (IAps f _ es) = size f + sum (map size es) + length es
size (ILAM _ _ e) = size e
size _ = 0
-}

isTriv :: IExpr a -> Bool
isTriv (IVar _) = True
-- do not inline ActionValue constants
-- may break correlations for foreign functions
isTriv (ICon _ ci) | isitActionValue_ t || isitActionValue t = False
  where t = iConType ci
isTriv (ICon _ (ICInt { })) = True
isTriv (ICon _ (ICReal { })) = True
isTriv (ICon _ (ICChar { })) = True
isTriv (ICon _ (ICString { })) = True
isTriv (ICon _ (ICUndet { })) = True
isTriv (ICon _ (ICTuple { fieldIds = [] })) = True
isTriv (ICon _ (ICDef { })) = True
isTriv _ = False

isHarmless :: IExpr a -> Bool
isHarmless e =
        --trace (ppReadable (e, onlySimple e, isPerm [] e)) $
        onlySimple e && isPerm [] e

-- expression is a proper combinator: somehow permutes arguments and constants
-- has no free variables and no embedded lambda expressions
--   is: accumulated list of lambda-bound parameters
isPerm :: [Id] -> IExpr a -> Bool
isPerm is (ILAM _ _ e) = isPerm is e
isPerm is (ILam i _ e) = isPerm (i:is) e
isPerm is e = null (gVars e \\ is)

gVars :: IExpr a -> [Id]
gVars (ILam i t e) = gVars e
gVars (IVar i) = [i]
gVars (ILAM i _ e) = gVars e
gVars (IAps f ts es) = gVars f ++ concatMap gVars es
gVars (ICon _ _) = []
gVars (IRefT _ _ _ _) = []

-- computes the top-level definitions the expression depends onb
-- dVars :: IExpr a -> [Id]
-- dVars (ILam _ _ e) = dVars e
-- dVars (IVar _) = []
-- dVars (ILAM _ _ e) = dVars e
-- dVars (IAps f _ es) = dVars f ++ concatMap dVars es
-- dVars (ICon i (ICDef { })) = [i]
-- dVars (ICon _ _) = []
-- dVars (IRefT _ _ _ _) = []

dVars :: IExpr a -> S.Set Id
dVars e = dVars' S.empty e

-- auxiliary function to guard against circular traversals
-- and to accumulate definitions that have been processed
dVars' :: S.Set Id -> IExpr a -> S.Set Id
dVars' ids (ILam _ _ e) = dVars' ids e
dVars' ids (IVar _) = ids
dVars' ids (ILAM _ _ e) = dVars' ids e
-- accumulate vars with a fold so we do not waste work processing the
-- same definitions over and over again across f and es.
dVars' ids (IAps f _ es) = foldl dVars' (dVars' ids f) es
-- guarding against circular traversal
dVars' ids (ICon i (ICDef { })) | i `S.member` ids = ids
dVars' ids (ICon i (ICDef {iConDef = e})) = dVars' (S.insert i ids) e
dVars' ids (ICon _ _) = ids
dVars' ids (IRefT _ _ _ _) = ids

onlySimple :: IExpr a -> Bool
onlySimple (ILam _ _ e) = onlySimple e
onlySimple (ILAM _ _ e) = onlySimple e
onlySimple (IAps f _ es) = onlySimple f && all onlySimple es
onlySimple (IVar _) = True
onlySimple (ICon _ (ICPrim { })) = True
onlySimple (ICon _ (ICInt { })) = True
onlySimple (ICon _ (ICReal { })) = True
onlySimple (ICon _ (ICChar { })) = True
onlySimple (ICon _ (ICString { })) = True
onlySimple (ICon _ (ICUndet { })) = True
onlySimple (ICon _ (ICTuple { fieldIds = [] })) = True
-- note that foreign function calls are not simple
onlySimple e = False

-----

-- should combine with FixupDefs

fixUpDefs :: [IDef a] -> [IDef a]
fixUpDefs ds =
    let m = M.fromList [ (i, e) | IDef i _ e _ <- ds ]
    in  iDefsMap (fixUp m) ds

fixUp :: M.Map Id (IExpr a) -> IExpr a -> IExpr a
fixUp m (ILam i t e) = ILam i t (fixUp m e)
fixUp m (ILAM i k e) = ILAM i k (fixUp m e)
fixUp m (IAps f ts es) = IAps (fixUp m f) ts (map (fixUp m) es)
fixUp m (ICon i (ICDef t d)) = ICon i (ICDef t (M.findWithDefault d i m))
fixUp m e = e
