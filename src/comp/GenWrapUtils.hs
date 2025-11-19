-- common utils for GenWrap and GenFuncWrap
module GenWrapUtils where

import FStringCompat
import Util(rTake, rDrop)
import ErrorUtil
import Id
import Pragma
import PreIds
import CSyntax
import CType
import Undefined (UndefKind(..))

-- ====================

genSuffix :: String
genSuffix = ['\173']

fsGenSuffix :: FString
fsGenSuffix = mkFString genSuffix


-- Add the Internal Flag to the Id
addInternalProp :: Id -> Id
addInternalProp lid = addIdProp lid IdPGeneratedIfc

isGenId :: Id -> Bool
isGenId i = hasIdProp i IdPGeneratedIfc


-- ====================
-- Field and module rename utilities

-- A function to rename the top interface name -- should not rename port of the interface.
-- This needs to generate a unique name for the interface based on the pragmas
-- Therefore Ifc_ is different from Ifc_ {always_ready} etc
ifcIdRename :: [PProp] -> Id -> Id
ifcIdRename pps modid = addInternalProp (mkIdPost nm fsGenSuffix)
 where
  pos = getPosition modid
  nm = flattenUSId ((unQualId modid) : (relevantNames pps))
  relevantNames :: [PProp] -> Longname
  relevantNames []                           = []
  relevantNames ((PPalwaysReady is):ps)      = (pp "AR") : (concat is) ++ (relevantNames ps)
  relevantNames ((PPalwaysEnabled is):ps)    = (pp "AE") : (concat is) ++ (relevantNames ps)
  relevantNames ((PPenabledWhenReady is):ps) = (pp "EWR") : (concat is) ++ (relevantNames ps)
  relevantNames (p:ps)                       = relevantNames ps
  pp s = mkId pos (mkFString s)

-- For now this just adds an underscore
modIdRename :: [PProp] -> Id -> Id
modIdRename pps modid = addInternalProp (mkIdPost (unQualId modid) fsGenSuffix)

dropGenSuffix :: String -> String
dropGenSuffix s =
    let sufLength = length genSuffix
        hasSuf = (length s > length genSuffix) &&
                 (rTake sufLength s == genSuffix)
    in  if (hasSuf)
        then rDrop sufLength s
        else internalError ("dropGenSuffix: " ++ s)

dropGenSuffixId :: Id -> Id
dropGenSuffixId i =
    let base' = dropGenSuffix (getIdBaseString i)
    in  setIdBaseString i base'

-- ====================

getDefArgs :: [CClause] -> CType -> [(Id, CType)]
getDefArgs dcls t =
   let (ts, _) = getArrows t
       vs = take (length ts) tmpVarIds
       -- preserve function/module argument names, if possible
       guessArgName (CPVar li, _) = li
       guessArgName (_      , lv) = lv
       vs' = case dcls of
              [CClause ps _ _] -> let new_vs = map guessArgName (zip ps vs)
                                  -- add the dropped elements of vs to ensure
                                  -- that vs and vs' have the same length
                                  in new_vs ++ (drop (length new_vs) vs)
              _ -> vs
   in  -- check that guessArgName didn't lose any arguments
       if (length vs' /= length ts)
       then internalError ("GenWrapUtils.getDefArgs: " ++
                           (show ((length vs'), (length ts))))
       else zip vs' ts

-- ====================

mkTypeProxyExpr :: CType -> CExpr
mkTypeProxyExpr ty = CHasType (CAny (getPosition ty) UNotUsed) $ CQType [] ty


