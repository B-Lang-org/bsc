module IInlineUtil(iSubst, iSubstWhen, iSubstIfc) where
import qualified Data.Map as M

import ErrorUtil(internalError)
import ISyntax
import ISyntaxUtil(irulesMap)
import Id
import PPrint(ppReadable)
import Util(fromJustOrErr)

iSubst :: M.Map Id (IExpr a) -> M.Map Id (IExpr a) -> IExpr a -> IExpr a
iSubst = iSubstWhen (const True)

-- TODO: The tst could be removed from this by cleaning up the smap in the callers
-- See https://github.com/B-Lang-org/bsc/pull/107#discussion_r390037780
iSubstWhen :: (IExpr a -> Bool) -> M.Map Id (IExpr a) -> M.Map Id (IExpr a) -> IExpr a -> IExpr a
iSubstWhen tst subMap defMap e = sub e
  where sub (IAps f ts es) = IAps (sub f) ts (map sub es)
        sub d@(ICon i val@(ICValue {})) =
            case M.lookup i subMap of
            Nothing ->
              let ev = fromJustOrErr ("iSubstWhen ICValue def not found: " ++ ppReadable i)
                                     (M.lookup i defMap)
              in ICon i (val { iValDef = ev })
            Just e -> if tst e then e else d
        sub u@(ICon i (ICUndet t k (Just v))) = ICon i (ICUndet t k (Just (sub v)))
        sub c@(ICon {}) = c
        sub ee = internalError ("iSubstWhen: " ++ ppReadable ee)


iSubstIfc :: M.Map Id (IExpr a) -> M.Map Id (IExpr a) -> IEFace a -> IEFace a
iSubstIfc smap dmap (IEFace i xs me mrs wp fi) = IEFace i xs me' mrs' wp fi
  where me'  = fmap (\(e, t) -> (iSubst smap dmap e, t)) me
        mrs' = fmap (irulesMap (iSubst smap dmap)) mrs
