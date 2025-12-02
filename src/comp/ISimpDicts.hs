-- Simplify lifted dicts so they can be inlined by isimplify
module ISimpDicts(iSimpDicts) where

import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace(trace)

import CType
import ISyntax
import ISyntaxSubst
import ISyntaxUtil
import Id
import Prim
import Pragma(PProp(..))
import Error(internalError)
import PPrint(ppReadable)

-- Expand lifted dictionary CAFs to manifest ICTuple form
-- This enables ISimplify to inline them efficiently

itIsDictType :: IType -> Bool
itIsDictType t
  | null $ fst $ itGetArrows t,
    ITCon _ _ (TIstruct SClass _) <- leftmost t = True
itIsDictType _ = False

iSimpDicts :: IPackage a -> IPackage a
iSimpDicts pkg@(IPackage { ipkg_defs = ds }) = pkg { ipkg_defs = ds'' }
  where ds' = map simpDict ds
        m = M.fromList [ (i, e') | IDef i _ e' _ <- ds' ]
        ds'' = iDefsMap (fixUp m) ds'

simpDict :: IDef a -> IDef a
simpDict (IDef i t e ps)
  | isLiftedDict i || itIsDictType t = IDef i t e'' ps
      where e' = simpExpr e
            isTuple = case e' of
                        ICon _ (ICTuple { }) -> True
                        IAps (ICon _ (ICTuple { })) _ _ -> True
                        _ -> False
            e'' = if isTuple
                  then trace (ppReadable i ++ " reduced to a ICTuple") $ e'
                  else trace (ppReadable i ++ " did not reduce to a ICTuple: " ++ ppReadable e' ++ "\n" ++ show e') e'
simpDict def = def

isLiftedDict :: Id -> Bool
isLiftedDict i = hasIdProp i IdPCAF && hasIdProp i IdPDict

-- Check if this is any dictionary-related definition
isDictDef :: Id -> Bool
isDictDef i = hasIdProp i IdPDict

simpExpr :: IExpr a -> IExpr a
simpExpr (ILAM i k e) = ILAM i k $ simpExpr e
simpExpr (ILam i t e) = ILam i t $ simpExpr e
simpExpr (IAps (ICon i (ICDef _ f)) ts es)
  | isDictDef i = simpAp f ts es
simpExpr (IAps f ts es) = simpAp f ts es
simpExpr e = e

simpAp :: IExpr a -> [IType] -> [IExpr a] -> IExpr a
simpAp (ILAM i _ e) (t:ts) es = simpAp (etSubst i t e) ts es
simpAp (ILam i _ b) [] (e:es) = simpAp (eSubst i e b) [] es
simpAp f [] [] = case f of
                   IAps f' ts es -> simpAp f' ts es
                   _ -> f
simpAp f ts es = IAps f ts es

-- Fix up ICDef nodes to point to definitions in the map (like fixUpDefs in ISimplify)
fixUp :: M.Map Id (IExpr a) -> IExpr a -> IExpr a
fixUp m (ILam i t e) = ILam i t (fixUp m e)
fixUp m (ILAM i k e) = ILAM i k (fixUp m e)
fixUp m (IAps f ts es) = IAps (fixUp m f) ts (map (fixUp m) es)
fixUp m (ICon i (ICDef t d)) = ICon i (ICDef t (M.findWithDefault d i m))
fixUp _ e = e
