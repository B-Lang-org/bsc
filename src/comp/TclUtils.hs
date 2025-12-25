{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module TclUtils(
    ExpandInfoBag(..),
    ExpandInfoHelper(..),
    checkEmptyList,
    eieDump,
    eieSearch,
    eMsgsToTcl,
    genId,
    getChildren,
    getEIElement,
    getInfo,
    getPositionPair,
    initExpandInfoBag,
    isRealPosition,
    lookupEIElement,
    lookupError,
    reportErrorsToTcl,
    showTaggedPosition,
    tclPosition,
    toPrintable,
    toPrintableDEBUG,
) where

--------
import Data.Char(isPrint,ord)
import Data.List(elemIndices)
import Control.Monad(foldM, unless)
import Text.Regex
import Text.Printf(printf)
import System.IO(hPutStr, stderr)
import qualified Data.Map as Map

import HTcl
import Error(internalError, EMsg, WMsg, showErrorList, showWarningList)
import PPrint
import PFPrint
import Id
import CSyntax
import ISyntax
import Pragma(DefProp(..))
import SymTab
import Assump
import Scheme
import Position
import FStringCompat
import FileNameUtil(baseName, getFullFilePath, getRelativeFilePath, dropSuf)
import Util(fst3)

---------------------------------------------
-- generate a qualified ID from the string Foo::x
genId :: String -> Id
genId s =  case (elemIndices ':' s)  of
             [] -> mk_homeless_id s
             [a,b] -> let q = take (a) s
                          n = drop (b+1) s
                      in setIdQualString  (mk_homeless_id n) q
             _  -> error $ "Ill formed identifier name: '" ++ s ++ "'"

--------------------------------------------------------------------------------
-- Error Handling

-- Expect an empty list otherwise throw an error
-- TODO might be a good place to add a new IOError error to hold the list and message
-- so it can be turned back to a regular tcl object.
checkEmptyList :: (Show a) => String -> [a] -> IO ()
checkEmptyList _ [] = return ()
checkEmptyList ms os = ioError $ userError ( ms ++ "\n" ++ show os)

-- --------------------------------------------------------------------

lookupError :: String -> String -> IO a
lookupError o s = ioError $ userError ( "Could not find a \""
                                         ++ o ++ "\" object with name \""
                                         ++ s ++ "\"." )


-- pass bluespec errors back to Tcl land  ie  $errorInfo
-- warnings are sent to stderr

reportErrorsToTcl :: [WMsg] -> [EMsg] -> IO ()
reportErrorsToTcl wms ems = do
  unless (null wms) $ hPutStr stderr (showWarningList wms)
  if null ems
  then return ()
  else eMsgsToTcl ems

eMsgsToTcl :: [EMsg] -> IO a
eMsgsToTcl [] = ioError $ userError "Unknown Error"
eMsgsToTcl ems = do
  let s = showErrorList ems
  error s


-------------------------------------------------------------------------------
-- Instances for bsc specific types
instance TclObjCvt Doc where
    toTclObj = toTclObj . toPrintable . docToOneLine

instance TclObjCvt Id where
    toTclObj i = toTclObj (pfpString i)

instance TclObjCvt (IDef a) where
    toTclObj (IDef i it _ie ps) = do --- why is expr dropped? XXX
      ti <- toTclObj i
      tit <- toTclObj it
      tps <- toTclObj ps
      toTclObj (TLst [TStr "IDef", TCL ti, TCL tit, TCL tps])

instance TclObjCvt DefProp where
  toTclObj (DefP_Rule i) = do ti <- toTclObj i ; toTclObj (TLst [TStr "DefP_Rule", TCL ti])
  toTclObj (DefP_Method i) = do ti <- toTclObj i ; toTclObj (TLst [TStr "DefP_Method", TCL ti])
  toTclObj (DefP_Instance i) = do ti <- toTclObj i ; toTclObj (TLst [TStr "DefP_Instance", TCL ti])
  toTclObj DefP_NoCSE = toTclObj "DefP_NoCSE"

instance TclObjCvt Type where
    toTclObj x = toTclObj (pfPrint PDReadable 0 x)

instance TclObjCvt Kind where
    toTclObj x = toTclObj (pfPrint PDReadable 0 x)

-- XXX
instance TclObjCvt IType where
    toTclObj (ITForAll i ik it) = do
                           ti <- toTclObj i
                           tit <- toTclObj it
                           tik <- toTclObj ik
                           toTclObj (TLst [TStr "ITForAll", TCL ti, TCL tik])
    toTclObj (ITAp t1 t2) =
                           toTclObj (TLst [TStr "ITAP", TStr (show t1), TStr (show t2)])
    toTclObj (ITVar i) = do
                           ti <- toTclObj i
                           toTclObj (TLst [TStr "ITVar", TCL ti])
    toTclObj (ITCon i ik tis) = do
                           ti <- toTclObj i
                           toTclObj (TLst [TStr "ITCon", TCL ti])
    toTclObj (ITNum n) = do
      tn <- toTclObj n
      toTclObj (TLst [TStr "ITNum", TCL tn])
    toTclObj (ITStr s) = do
      tn <- toTclObj $ getFString s
      toTclObj (TLst [TStr "ITStr", TCL tn])

instance TclObjCvt IKind where
    toTclObj k = toTclObj (pPrint PDReadable 0 k)

instance TclObjCvt IdK where
    toTclObj k = toTclObj (pfPrint PDReadable 0 k)

-- XXX incomplete
instance TclObjCvt CDefn where
    toTclObj k@(Cdata {} ) = toTclObj (pfPrint PDReadable 0 k)
    toTclObj k = case getName k of
                   Right i -> toTclObj i
                   Left p  -> toTclObj (dummyId p)
    --toTclObj k = toTclObj (pPrint PDReadable 0 k)
    --toTclObj (Ctype k ids ct)

-- ?? Take care of ID
instance TclObjCvt Assump where
    toTclObj (i :>: s) = toTclObj s

instance TclObjCvt Scheme where
    toTclObj x = toTclObj (pfPrint PDReadable 0 x)

-- Conversion for SymTab Types
instance TclObjCvt VarInfo where
    toTclObj (VarInfo vk a d _) = do
        ta <- toTclObj a
        tk <- toTclObj (show vk)
        td <- toTclObj d
        toTclObj $ TLst [TCL tk, TCL ta, TCL td]

instance TclObjCvt ConInfo where
    toTclObj (ConInfo i v a cti _) = do
                             ti <- toTclObj i
                             ta <- toTclObj a
                             toTclObj $ TLst [TCL ti, TCL ta]

instance TclObjCvt TypeInfo where
    toTclObj (TypeInfo mi k vs tis _) = do
                              i <- toTclObj (maybe "??" getIdString mi)
                              tk <- toTclObj k
                              tvs <- toTclObj vs
                              ttis <- toTclObj tis
                              toTclObj $ TLst [TCL i, TCL tk, TCL tvs, TCL ttis]

instance TclObjCvt TISort where
    toTclObj (TItype i t) = do
                            tfs <- toTclObj t
                            toTclObj $ TLst [TStr "alias", TCL tfs]

    toTclObj (TIdata is enum)  = do
                            tfs <- mapM toTclObj is
                            let name = if enum then "enum" else "union"
                            toTclObj $ TLst [TStr name, TLst (map TCL tfs)]

    toTclObj (TIstruct SStruct fs) = do
                            tfs <- mapM toTclObj fs
                            toTclObj $ TLst [TStr "structure", TLst (map TCL tfs)]

    toTclObj (TIstruct SClass fs) = do
                            tfs <- mapM toTclObj fs
                            toTclObj $ TLst [TStr "class", TLst (map TCL tfs)]

    toTclObj (TIstruct (SDataCon i _) fs) = do
                            tfs <- mapM toTclObj fs
                            toTclObj $ TLst [TStr "DataCon", TLst (map TCL tfs)]

    toTclObj (TIstruct (SInterface ps) fs) = do
                            tfs <- mapM toTclObj fs
                            toTclObj $ TLst [TStr "interface", TLst (map TCL tfs)]

    toTclObj (TIstruct (SPolyWrap _ _ _) fs) = do
                            tfs <- mapM toTclObj fs
                            toTclObj $ TLst [TStr "PolyWrap", TLst (map TCL tfs)]

    toTclObj TIabstract = toTclObj "Abstract"


instance TclObjCvt FieldInfo where
    toTclObj x = toTclObj $ pPrint PDReadable 0 x


instance TclObjCvt Position where
    toTclObj pos = toTclObj $ tclPosition pos

tclPosition :: Position -> [String]
tclPosition  (Position fs l c pred) =
    let f = getFString fs
        rf = getRelativeFilePath f
        ff = getFullFilePath f
        bf = addBSDir ff
        pf = if bf == ff then rf else bf
        base_name = baseName f
        lib = dropSuf base_name
    in if l==(-2) && c<0 && f=="" then ["Command","",""] else
           if l<0 && c<0 && f=="" then ["Unknown","",""] else
               if pred then [pf, show l, show c, "Library " ++ lib] else
               [pf, show l, show c]

addBSDir :: String -> String
addBSDir ff | ff' /= ff = ff'
 where regex = mkRegex "^[ ]*/.+/src/Libraries/Base.+/"
       ff'   = subRegex regex ff "%/Libraries/"
addBSDir ff = ff

showTaggedPosition :: (HasPosition a) => a -> [HTclObj]
showTaggedPosition i =
    let pos = getPosition i
        res = [tagManyStr "position" (tclPosition pos)]
        isUseful = isRealPosition pos
    in  if isUseful then res else []

getPositionPair :: (HasPosition a) => a -> [HTclObj]
getPositionPair i =
    let pos = getPosition i
        res = [TStr "position",  positionToTObj pos]
        isUseful = isRealPosition pos
    in  if isUseful then res else []

isRealPosition :: Position -> Bool
isRealPosition pos@(Position fs line column pred) =
    pos /= noPosition

--------------------------------------------------------------------------
-- Help functions and structure for dealing with hierarchy trees in an easy way

data ExpandInfoBag a = ExpandInfoBag { mbag         :: Map.Map Int (ExpandInfoElem a)
                                     ,maxIdx        :: Int
                                     }

initExpandInfoBag ::  ExpandInfoBag a
initExpandInfoBag = ExpandInfoBag { mbag    = Map.singleton 0 Root
                                  ,maxIdx   = 0
                                  }

-- TODO this can be generalize from IO to Monad
class ExpandInfoHelper a where
    getRootElem :: IO a  -- The root element
    getChildrenf :: a -> IO [a]
    getTextf     :: a -> IO String
    getTagsf     :: a -> IO [String]
    getInfof     :: a -> IO HTclObj

-- TODO add left| branch attr to tuple for iwidgets
type EIDisplay = [(Int,String,[String])]

data ExpandInfoElem a = Root -- unpopulated tree
                      |TrueLeaf a
                      | CurrentLeaf a
                      | Branch a EIDisplay

getEIElement :: ExpandInfoElem a -> a
getEIElement Root            = internalError ("TclUtil::getEIElement Root")
getEIElement (TrueLeaf x)    = x
getEIElement (CurrentLeaf x) = x
getEIElement (Branch x _)    = x


eieDump :: ExpandInfoHelper a => ExpandInfoBag a -> IO [HTclObj]
eieDump bag =
    do
      let
          genOneObj :: ExpandInfoHelper a => (Int,ExpandInfoElem a) -> IO HTclObj
          genOneObj (k,o) = do
            i <- case o of
                   Root  -> return $ TStr "Root"
                   _     -> getTextf (getEIElement o) >>= (return .  TStr)
            return $ TLst [TInt k, i]
      mapM genOneObj (Map.toList (mbag bag))

-- flow is to lookup,  then update the global state and then return
getChildren :: ExpandInfoHelper a => ExpandInfoBag a -> Int -> IO (ExpandInfoBag a, EIDisplay)
getChildren bagin key =
    let
        updateCurrent :: ExpandInfoElem a -> ExpandInfoBag a ->  ExpandInfoBag a
        updateCurrent elem b = b { mbag = Map.insert key elem (mbag b)}
        --
        -- expansion for a current leaf
        expandCLeaf :: (ExpandInfoHelper a) => [a] -> ExpandInfoBag a -> IO (ExpandInfoBag a, EIDisplay)
        expandCLeaf [] bag = return (bag,[])
        expandCLeaf cas bag = do
          let
              -- next set of indexes
              nextIndexs :: [Int]
              nextIndexs = [(1 + maxIdx bag) ..]
              -- new elements for the bag
              eileafs = (map CurrentLeaf cas)
              newElems = Map.fromList (zip nextIndexs eileafs)
              m' = Map.union newElems (mbag bag)
              b' = bag { mbag = m', maxIdx = maxIdx bag + length cas }

          -- generate the displaed text
          cTestStrs <- mapM getTextf cas
          tags      <- mapM getTagsf  cas
          let
              children :: EIDisplay
              children = zip3 nextIndexs cTestStrs tags
          return (b', children)
        --
    --
    in case lookupEIElement bagin key of
         Root          -> do root <- getRootElem
                             cas  <- getChildrenf root
                             (b',d) <- expandCLeaf cas bagin
                             let replaceElem = if null cas then TrueLeaf root
                                               else Branch root d
                                 b'' = updateCurrent replaceElem b'
                             return (b'',d)
         TrueLeaf x    -> return (bagin, [])
         CurrentLeaf x -> do cas <- getChildrenf x
                             (b',d) <- expandCLeaf cas bagin
                             let replaceElem = if null cas then TrueLeaf x
                                               else Branch x d
                                 b'' = updateCurrent replaceElem b'
                             return (b'',d)

         Branch x d    -> return (bagin,d)

getInfo :: ExpandInfoHelper a => ExpandInfoBag a -> Int -> IO HTclObj
getInfo b key = getInfof (getRawEIElement b key)

getRawEIElement ::  ExpandInfoBag a -> Int -> a
getRawEIElement b key = getEIElement $ lookupEIElement b key

lookupEIElement ::  ExpandInfoBag a -> Int -> ExpandInfoElem a
lookupEIElement b key = let err = error ("lookupEIElement: Invalid lookup of element " ++ show key)
                        in Map.findWithDefault err key (mbag b)

eieSearch :: (ExpandInfoHelper a) => (a -> Bool)  -> ExpandInfoBag a -> IO (ExpandInfoBag a, [EIDisplay])
eieSearch testf obag = do
  let searchLevel path (bag,found) key = do
            (bag',children) <- getChildren  bag key
            let elem = getRawEIElement bag' key
            s <- getTextf elem
            t <- getTagsf elem
            let path'  = if key /= 0 then (key,s,t):path else path
                found' = if testf elem then (reverse path'):found else found
            foldM (searchLevel path') (bag',found') (map fst3 children)
  searchLevel [] (obag,[]) 0

positionToTObj ::  Position -> HTclObj
positionToTObj p = toHTObj $ tclPosition p

-----------------------------------------------------------------------------
instance HTclObjCvt Doc where
    toHTObj = TStr . toPrintable . docToOneLine

instance HTclObjCvt Id  where
    toHTObj i = toHTObj $  pfPrint PDReadable 0 i

instance HTclObjCvt CType where
    toHTObj i = toHTObj $ pfPrint PDReadable 0 i

instance HTclObjCvt Position  where
    toHTObj p = toHTObj $ tclPosition p

instance (HTclObjCvt a) => HTclObjCvt (Maybe a)  where
    toHTObj (Just i) = tag "Just" [toHTObj i]
    toHTObj Nothing  = TStr "Nothing"

instance HTclObjCvt [EMsg] where
    toHTObj es = toHTObj $ showErrorList es


------------------------------------------------------------------------
toPrintable :: String -> String
toPrintable = filter isPrint

toPrintableDEBUG :: String -> String
toPrintableDEBUG = concatMap toPrintable'
    where toPrintable' c | isPrint c = [c]
                         | otherwise = printf "<%X>" (ord c)
