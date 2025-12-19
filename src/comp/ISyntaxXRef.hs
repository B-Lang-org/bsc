module ISyntaxXRef(
                   updateIExprPosition,
                   updateITypePosition,
                   mapIExprPosition,
                   mapIExprPosition2,
                   mapIExprPositionConservative
                  ) where

import qualified Data.Set as S

import ISyntax
import Id
import Position(Position, noPosition, isUsefulPosition)

-- #############################################################################
-- #
-- #############################################################################

updateIExprPosition :: Position -> IExpr a -> IExpr a
updateIExprPosition pos (ILam i t e) = (ILam (setIdPosition pos i) t (updateIExprPosition pos e))
updateIExprPosition pos (IAps e ts [e0]) = (IAps (updateIExprPosition pos e) ts [(updateIExprPosition pos e0)])
updateIExprPosition pos (IAps e ts es) = (IAps (updateIExprPosition pos e) ts es)
updateIExprPosition pos (IVar i) = (IVar (setIdPosition pos i))
updateIExprPosition pos (ILAM i kind e) = (ILAM (setIdPosition pos i) kind (updateIExprPosition pos e))
updateIExprPosition pos iexpr@(ICon i (ICStateVar t isv)) = iexpr
updateIExprPosition pos (ICon i info) = (ICon (setIdPosition pos i) info)
updateIExprPosition pos (IRefT t p poss r) = (IRefT (updateITypePosition pos t) p poss' r)
  where poss' = S.insert pos poss

updateITypePosition :: Position -> IType -> IType
updateITypePosition pos (ITForAll i kind t) = (ITForAll (setIdPosition pos i) kind t)
updateITypePosition pos (ITAp t t') = (ITAp (updateITypePosition pos t) (updateITypePosition pos t'))
updateITypePosition pos (ITVar i) = (ITVar (setIdPosition pos i))
updateITypePosition pos (ITCon i kind sort) = (ITCon (setIdPosition pos i) kind sort)
updateITypePosition pos t@(ITNum _) = t
updateITypePosition pos t@(ITStr _) = t


updateIExprPosition2 :: Position -> IExpr a -> IExpr a
updateIExprPosition2 pos (ILam i t e) = (ILam (setIdPosition pos i) t (updateIExprPosition pos e))
updateIExprPosition2 pos iexpr@(IAps e@(ICon i (ICCon _ _)) ts [e0]) =
    if (not (isUsefulPosition (getIdPosition i)))
    then updateIExprPosition pos iexpr
    else iexpr
updateIExprPosition2 pos iexpr@(IAps e@(ICon i (ICPrim _ _)) ts es) =
    if (not (isUsefulPosition (getIdPosition i)))
    then updateIExprPosition pos iexpr
    else iexpr
updateIExprPosition2 pos (IAps e ts [e0]) = (IAps (updateIExprPosition pos e) ts [(updateIExprPosition pos e0)])
updateIExprPosition2 pos (IAps e ts es) = (IAps (updateIExprPosition pos e) ts es)
updateIExprPosition2 pos (IVar i) = (IVar (setIdPosition pos i))
updateIExprPosition2 pos (ILAM i kind e) = (ILAM (setIdPosition pos i) kind (updateIExprPosition pos e))
updateIExprPosition2 pos iexpr@(ICon i (ICStateVar t isv)) = iexpr
updateIExprPosition2 pos (ICon i info) = (ICon (setIdPosition pos i) info)
updateIExprPosition2 pos (IRefT t p poss r) = (IRefT (updateITypePosition pos t) p poss' r)
  where poss' = S.insert pos poss

mapIExprPosition :: Bool -> (IExpr a, IExpr a) -> IExpr a
mapIExprPosition False (expr_0, expr_1) = expr_1
mapIExprPosition True (expr_0, expr_1) =
    let positionModel = (getIExprPositionCross expr_0)
    in if (positionModel == noPosition) || (not (isUsefulPosition positionModel))
       then expr_1
       else let positionCurrent = (getIExprPositionCross expr_1)
            in if (positionModel == positionCurrent)
               then expr_1
               else if (isEquivIExprIncluded expr_1 expr_0)
                    then let pos = (getIExprPositionCross (head (extractEquivIExpr expr_1 expr_0)))
                             expr = (updateIExprPosition pos expr_1)
                         in expr
                    else (updateIExprPosition positionModel expr_1)

mapIExprPosition2 :: Bool -> (IExpr a, IExpr a) -> IExpr a
mapIExprPosition2 False (expr_0, expr_1) = expr_1
mapIExprPosition2 True (expr_0, expr_1) =
    let positionModel = (getIExprPositionCross expr_0)
    in if (positionModel == noPosition) || (not (isUsefulPosition positionModel))
       then expr_1
       else let positionCurrent = (getIExprPositionCross expr_1)
            in if (positionModel == positionCurrent)
               then expr_1
               else if (isEquivIExprIncluded expr_1 expr_0)
                    then let pos = (getIExprPositionCross (head (extractEquivIExpr expr_1 expr_0)))
                             expr = (updateIExprPosition2 pos expr_1)
                         in expr
                    else (updateIExprPosition2 positionModel expr_1)

mapIExprPositionConservative :: Bool -> (IExpr a,IExpr a) -> IExpr a
mapIExprPositionConservative False (expr_0, expr_1) = expr_1
mapIExprPositionConservative True (expr_0, expr_1) =
    let positionModel = (getIExprPositionCross expr_0)
    in if (positionModel == noPosition) || (not (isUsefulPosition positionModel))
       then expr_1
       else let positionCurrent = (getIExprPositionCross expr_1)
            in if (positionModel == positionCurrent) || (isUsefulPosition positionCurrent)
               then expr_1
               else if (isEquivIExprIncluded expr_1 expr_0)
                    then let pos = (getIExprPositionCross (head (extractEquivIExpr expr_1 expr_0)))
                             expr = (updateIExprPosition pos expr_1)
                         in expr
                    else (updateIExprPosition positionModel expr_1)

-- #############################################################################
-- #
-- #############################################################################

isEquivIExprIncluded :: IExpr a -> IExpr a -> Bool
isEquivIExprIncluded sub_expr expr@(ILam i t e) =
    ((equivIExprs expr sub_expr) || (isEquivIExprIncluded sub_expr e))
isEquivIExprIncluded sub_expr expr@(IAps e ts es) =
    ((equivIExprs expr sub_expr) || (or (map (equivIExprs sub_expr) es)))
isEquivIExprIncluded sub_expr expr@(IVar _) =
    (equivIExprs expr sub_expr)
isEquivIExprIncluded sub_expr expr@(ILAM i kind e) =
    ((equivIExprs expr sub_expr) || (isEquivIExprIncluded sub_expr e))
isEquivIExprIncluded sub_expr expr@(ICon _ _) =
    (equivIExprs expr sub_expr)
isEquivIExprIncluded sub_expr expr@(IRefT t p poss r) =
    (equivIExprs expr sub_expr)

-- #############################################################################
-- #
-- #############################################################################

extractEquivIExpr :: IExpr a -> IExpr a -> [IExpr a]
extractEquivIExpr sub_expr expr@(ILam i t e) = if (equivIExprs sub_expr expr)
                                               then [expr]
                                               else (extractEquivIExpr sub_expr e)

extractEquivIExpr sub_expr expr@(IAps e ts es) = if (equivIExprs sub_expr expr)
                                                 then [expr]
                                                 else (concatMap (extractEquivIExpr sub_expr) es)

extractEquivIExpr sub_expr expr@(IVar _) =  if (equivIExprs sub_expr expr)
                                            then [expr]
                                            else []

extractEquivIExpr sub_expr expr@(ILAM i kind e) =  if (equivIExprs sub_expr expr)
                                                   then [expr]
                                                   else (extractEquivIExpr sub_expr e)

extractEquivIExpr sub_expr expr@(ICon _ _) =  if (equivIExprs sub_expr expr)
                                              then [expr]
                                              else []

extractEquivIExpr sub_expr expr@(IRefT t p poss r) =  if (equivIExprs sub_expr expr)
                                                      then [expr]
                                                      else []

-- #############################################################################
-- #
-- #############################################################################

equivIExprs :: IExpr a -> IExpr a -> Bool
equivIExprs e0@(ILam i0 t0 ee0) e1@(ILam i1 t1 ee1) = ((equivId i0 i1) && (t0 == t1) && (ee0 == ee1))
equivIExprs e0@(IAps ee0 ts0 es0) e1@(IAps ee1 ts1 es1) = ((equivIExprs ee0 ee1) && (ts0 == ts1) && (es0 == es1))
equivIExprs e0@(IVar i0) e1@(IVar i1) = (equivId i0 i1)
equivIExprs e0@(ILAM i0 k0 ee0) e1@(ILAM i1 k1 ee1) = ((equivId i0 i1) && (k0 == k1) && (ee0 == ee1))
equivIExprs e0@(ICon i0 info0) e1@(ICon i1 info1) = ((equivId i0 i1) && (info0 == info1))
equivIExprs e0@(IRefT t0 p0 poss0 r0) e1@(IRefT t1 p1 poss1 r1) = (p0 == p1)
equivIExprs e0 e1 = False

equivId :: Id -> Id -> Bool
equivId id0 id1 = (id0 == id1) && (getIdProps id0 == getIdProps id1)

-- #############################################################################
-- #
-- #############################################################################
