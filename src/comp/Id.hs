{-# LANGUAGE FlexibleInstances, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fwarn-name-shadowing -fwarn-missing-signatures #-}

module Id(
        Id,
        mkId,
        mkQId,
        qualId,
        dummyId,
        emptyId,
        unq_eqs,
        getIdString,
        getIdQualString,
        getIdPosition,
        isEmptyId,
        isUnqualId,
        getIdFString,
        setIdQual,
        setIdQualString,
        enumId,
        setIdPosition,
        getIdBase,
        getIdBaseString,
        setIdBase,
        setIdBaseString,
        getIdQFString,
        getIdQual,
        unQualId,
        getIdFStrings,
        getFixity,
        cloneId,
        mkUId,
        qualEq,
        getIdFStringP,
        mkIdPre,
        mkIdPost,
        flattenUSId,
        mkUSId,
        mk_homeless_id, {- mk_homeless_qid, -} mk_dangling_id,
        mkTCId,
        isTCId,
        splitTCId,
        mkStId,
        mkNumId, mkStrId,
        mkRdyId, isRdyId,
        isKeepId, setKeepId, rmKeepId,
        isHideId, setHideId, rmHideId,
        isHideAllId, setHideAllId, rmHideAllId,
        isBadId, setBadId,
        isFromRHSId, setFromRHSId,
        isSignedId, setSignedId,
        setInternal,
        isDictId,
        isInternal,
        isSplitRuleId,
        isRuleId,
        mkSplitId,
        isRenamingId,
        IdProp(..),
        addIdProp,
        rmIdProp,
        rmIdPropBy,
        addIdProps, copyIdProps, hasIdProp, hasAnyIdProp, getIdProps, setIdProps,
        mkIdCanFire, mkIdWillFire, isIdCanFire, isIdWillFire, isFire, isIdEnable,
        mkIdRule,
        addIdSuffix,
        addId_Suffix,
        addId_Suffixes,
        addId_SuffixPadded,
        stripId_Suffix,
        addSuffix,
        removeSuffix,
        removeAllSuffixes,
        getSuffixCount,
        isSuffixCountProp,
        cmpSuffixedIdByName,
        mkEnableId,
        getFromReady,
        dropRulePrefix,
        dropRulePrefixId,
        dropWillFirePrefix,
        dropWillFirePrefixId,
        dropCanFirePrefix,
        dropCanFirePrefixId,
        dropReadyPrefixId,
        getIdTuple,
        dummy_id,
        cmpIdByName,
        Longname,
        createPositionString,
        genUniqueIdsAndMap,
        mkConcatId,
        mkIdTempReturn,
        addToQual,
        addToBase,
        show_full,
        idCompareWithPos,
        setNakedInstId,
        isNakedInstId,
        setIdDisplayName,
        getIdDisplayName,
        addIdDisplayName,
        getIdInlinedPositions,
        addIdInlinedPositions,
        removeIdInlinedPositions
         ) where

import Data.Char(isDigit, digitToInt)
import Data.List
import Data.Maybe
import qualified Data.Generics as Generic
import qualified Data.Map as Map

import Util(headOrErr, lastOrErr, ToString(..))
import FileNameUtil(dropSuf, takeSuf, getRelativeFilePath)
import Eval(NFData(..))
import ErrorUtil(internalError)
import FStringCompat
import Position
import Fixity
import PreStrings(fsUnderscore, fsUnderUnder, fsDot, fsTyJoin, fsEmpty, fsCanFire, fsWillFire, fsAVValue, fsMethodReturn, fs_unnamed)
import PreStrings(fs_rdy, fsEnable, fs_rl)
import IOUtil(progArgs)
--import Util(traces)

-- #############################################################################
-- # A new data type enumerating the various properties an Id might have.
-- #############################################################################

data IdProp = IdPCanFire
              | IdPWillFire
              | IdPProbe
              | IdPInternal
              | IdPReady                -- interface ready signal
              | IdPGeneratedIfc         -- generated interface name
              | IdPMeth
              | IdPCommutativeTCon      -- commutative type constructor
              | IdP_enable
              | IdP_keep
              | IdP_keepEvenUnused
              | IdPRule
              | IdPSplitRule
              | IdPDict                 -- is a dictionary
              | IdPRenaming             -- id for temporary renaming
              | IdP_suffixed            -- a _nn suffix has been added
              | IdP_SuffixCount Integer -- the number of suffixes added ... not to be used with IdP_suffixed
              | IdP_bad_name            -- a name generated without good information (e.g., __d5)
              | IdP_from_rhs            -- a name generated from the right-hand-side of an assignment (e.g., x_PLUS_5__d32)
              | IdP_signed              -- in C backend, an id created from $signed()
              | IdP_NakedInst           -- id associated with a "naked" instantiation (i.e. without a bind)
              | IdPDisplayName FString  -- provide an alternate display string
              | IdP_hide
              | IdP_hide_all
              | IdP_TypeJoin Id Id      -- Internally generated type name (anonymous structs)
                                        -- Arguments are the original type and constructor name
              | IdPMethodPredicate      -- is a predicate of a method call in a rule
              -- the Id of meth calls on imported/synthesized modules
              -- can be tagged with the position of inlined method calls
              -- that it was contained in (the top methods are last)
              | IdPInlinedPositions [Position]
              -- used by the BSV parser to keep track of which array types
              -- were introduced from bracket syntax
              | IdPParserGenerated
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

-- #############################################################################
-- #
-- #############################################################################

data Id = Id { id_pos :: !Position,
               id_mfs :: !FString,
               id_fs :: !FString,
               id_props :: [IdProp] {- , id_stab :: Int -}
             }
     deriving (Generic.Data,Generic.Typeable)

show_raw_id :: Bool
show_raw_id = "-show-raw-id" `elem` progArgs

instance Show Id where
    show | show_raw_id = show_full
         | otherwise   = show_brief

show_brief :: Id -> String
show_brief i =
    case (getFString (id_mfs i), getFString (id_fs i)) of
    ("", str) -> add_props str
    (pkg, str) -> add_props (pkg ++ "::" ++ str)
  where add_props str | null (id_props i) = str
                      | otherwise = str ++ show (id_props i)

-- show_full uses positional pattern-matching to make sure all parts are shown
show_full :: Id -> String
show_full (Id pos mfs fs props) =
  "(Id (" ++ show pos ++ ") ("
          ++ show mfs ++ ") ("
          ++ show fs  ++ ") ("
          ++ show props ++ "))"

-- ### base access routines
setIdBase :: Id -> FString -> Id
setIdBase a fs = a { id_fs = fs }

getIdBase :: Id -> FString
getIdBase a = id_fs a

setIdQual :: Id -> FString -> Id
setIdQual a fs = a { id_mfs = fs }

getIdQual :: Id -> FString
getIdQual a = id_mfs a

getIdPosition :: Id -> Position
getIdPosition a = id_pos a

setIdPosition :: Position -> Id -> Id
setIdPosition p a = a { id_pos = p }

getIdProps :: Id -> [IdProp]
getIdProps a = id_props a

setIdProps :: Id -> [IdProp] -> Id
setIdProps a l = a { id_props = l }

instance Eq Id where
        a == b = idEq a b
-- XXX marking identifiers internal we shouldn't
-- tests fail with uncommenting
--             isInternal a == isInternal b

-- a separate function becomes a cost center for performance runs
idEq :: Id -> Id -> Bool
idEq a b = (id_fs a == id_fs b) && (id_mfs a == id_mfs b)

qualEq :: Id -> Id -> Bool
qualEq a b | getIdQual a == fsEmpty || getIdQual b == fsEmpty = getIdBase a == getIdBase b
qualEq a b = a == b

-- unqualified (base) Id equal-to-string
unq_eqs :: Id -> String -> Bool
unq_eqs idx str = getIdBaseString idx == str

instance Ord Id where
    compare  = idCompare

-- a separate function becomes a cost center for performance runs
idCompare :: Id -> Id -> Ordering
idCompare a b = case (compare (id_fs a) (id_fs b)) of
                EQ -> compare (id_mfs a) (id_mfs b)
                LT -> LT
                GT -> GT

-- to use when position matters
idCompareWithPos :: Id -> Id -> Ordering
idCompareWithPos a b = case (compare a b) of
                       EQ -> compare (getIdPosition a) (getIdPosition b)
                       LT -> LT
                       GT -> GT

cmpIdByName :: Id -> Id -> Ordering
i `cmpIdByName` i' = getIdString i `compare` getIdString i'

cmpSuffixedIdByName :: Id -> Id -> Ordering
cmpSuffixedIdByName x y =
        let count_x = getSuffixCount(x);
            count_y = getSuffixCount(y);
            default_x = (x, Nothing);
            default_y = (y, Nothing);
            addJust (a, b) = (a, Just b)
            pair_x = if (count_x == 0) then default_x else addJust $ removeSuffix x
            pair_y = if (count_y == 0) then default_y else addJust $ removeSuffix y
        in pair_x  `compare` pair_y

instance HasPosition Id where
    getPosition i = getIdPosition i

mkId :: Position -> FString -> Id
mkId pos fs =
    let value = Id pos fsEmpty fs []
    in -- trace("ID: " ++ (ppReadable value)) $
       value

mk_homeless_id :: String -> Id
mk_homeless_id s = mkId noPosition (mkFString s)

mk_dangling_id :: String -> Position -> Id
mk_dangling_id s p = mkId p (mkFString s)

-- Long names

type Longname = [Id]

-- Qualified with a path.
mkQId :: Position -> FString -> FString -> Id
mkQId pos mfs fs
    | fs == fsEmpty = Id pos fsEmpty fsEmpty []
    | isDigit (head (getFString fs)) = Id pos fsEmpty fs [] -- XXX
    | otherwise = Id pos mfs fs []

-- Qualify  id(2) with the name from id(1)   join id properties.
qualId :: Id -> Id -> Id
qualId a i = addIdProps (setIdQual i (getIdBase a)) (getIdProps a)

-- remove qualification
unQualId :: Id -> Id
unQualId a = setIdQual a fsEmpty

-- An id with just "_" as a name
dummyId :: Position -> Id
dummyId p = Id p fsEmpty fsUnderscore []

-- does an Id have no content whatsoever?
isEmptyId :: Id -> Bool
isEmptyId i = getIdBase i == fsEmpty

isUnqualId :: Id -> Bool
isUnqualId i = getIdQual i == fsEmpty

dummy_id :: Id
dummy_id = dummyId noPosition

-- Create an id of the form "<str>_<index>".
-- This is used to ENUMerate a list of Ids with the same name,
-- but with uniquifying numbers.
--
-- Note: The Ids created with this are marked as "bad".  If these Ids
-- need to be created from a user-given name, consider creating a new
-- interface for this which takes Id and not String, and derives its
-- properties from that Id.
enumId :: String -> Position -> Int -> Id
enumId str pos index =
    let id_str = tmpFString index ("_" ++ str ++ itos index)
    in  setBadId
            (Id pos fsEmpty id_str [])

createPositionString :: Position -> String
createPositionString pos =
    let file = (getRelativeFilePath (getPositionFile pos))
    in ((take 3 (dropSuf file)) ++ "." ++ (takeSuf file) ++ "_" ++ (show (getPositionLine pos)) ++ "_" ++ (show (getPositionColumn pos)))

getIdString :: Id -> String
getIdString a | mfs == fsEmpty = getFString fs
              | otherwise = getFString mfs ++ "." ++ getFString fs
    where mfs = getIdQual a
          fs = getIdBase a

getIdBaseString :: Id -> String
getIdBaseString a = getFString $ getIdBase a

setIdBaseString :: Id -> String -> Id
setIdBaseString idx str = setIdBase idx (mkFString str)

getIdQualString :: Id -> String
getIdQualString a = getFString $ getIdQual a

setIdQualString :: Id -> String -> Id
setIdQualString a str = setIdQual a (mkFString str)

getIdFStrings :: Id -> (FString, FString)
getIdFStrings a = (getIdQual a, getIdBase a)

getIdQFString :: Id -> Maybe FString
getIdQFString a = if getIdQual a == fsEmpty then Nothing else Just (getIdQual a)

getIdFString :: Id -> FString
getIdFString a = if getIdQual a == fsEmpty then getIdBase a else concatFString [getIdQual a, fsDot, getIdBase a]

getIdFStringP :: Id -> FString
getIdFStringP a =
    let mfs = getIdQual a
        fs = getIdBase a
    in if mfs == fsEmpty then fs else
        case getFString fs of
        "->" -> fs
        c:_ | isDigit c -> fs
        _ -> concatFString [mfs, fsDot, fs]

getIdTuple :: Id -> (Position, String)
getIdTuple i = (getIdPosition i, getIdString i)

-- Join the names from the list on the second id
cloneId :: [Id] -> Id -> Id
cloneId is a = setIdBase a (cloneFString (map getIdFString is) (getIdBase a))

getFixity :: Id -> Fixity
getFixity i =
    case getIdBaseString i of
    ","   -> FInfixr (-1)
{-
    "$"   -> FInfixr 0

    ":="  -> FInfixr 1

    "||"  -> FInfixr 2
    "&&"  -> FInfixr 3

    "|"   -> FInfixl 4
    "&"   -> FInfixl 5

    "=="  -> FInfix  6
    "/="  -> FInfix  6
    "<="  -> FInfix  6
    ">="  -> FInfix  6
    "<"   -> FInfix  6
    ">"   -> FInfix  6

    "<<"  -> FInfix  7
    ">>"  -> FInfix  7

    "++"  -> FInfixr 8
    ":>"  -> FInfixr 8

    "+"   -> FInfixl 10
    "-"   -> FInfixl 10

    "*"   -> FInfixl 11
    "/"   -> FInfixl 11

    "\xbb"-> FInfixr 12 -- https://en.wikipedia.org/wiki/Guillemet or '>>'

    "\xb7"-> FInfixr 13 -- https://en.wikipedia.org/wiki/Interpunct or '.'

    "|>"  -> FInfixr 15
-}
    _     -> defaultFixity
-- Prepends "_" to id name
mkUId :: Id -> Id
mkUId a = setIdBase a (concatFString [fsUnderscore, getIdBase a])

-- Join Ids
join2ids :: Id -> Id -> FString -> Id -> Id
join2ids pid a j b
    | isEmptyId a = b
    | isEmptyId b = a
    | otherwise   = addIdProps
                       (setIdBase pid
                           (concatFString [getIdBase a, j, getIdBase b]))
                       (union (getIdProps b) (getIdProps a))

-- Joins 2 ids with underscore connector
mkUSId :: Id -> Id -> Id
mkUSId a b = setIdQual (join2ids b a fsUnderscore b) (getIdQual a)

-- Convert a Longname to an Id using underscore as a connector
flattenUSId :: Longname -> Id
flattenUSId [] = Id noPosition fsEmpty fsEmpty [] -- (empty ID)
flattenUSId (i:is) = foldl mkUSId i is

-- The null identifier (used in base case of recursive functions):
emptyId :: Id
emptyId = flattenUSId []

-- Joins 2 ids with TyJoin connector
mkTCId :: Id -> Id -> Id
mkTCId a b = setIdProps (setIdQual (join2ids b a fsTyJoin b) (getIdQual a)) [IdP_TypeJoin a b]

isTCId :: Id -> Bool
isTCId = isJust . splitTCId

splitTCId :: Id -> Maybe (Id, Id)
splitTCId i = listToMaybe [ (a,b) | IdP_TypeJoin a b <- getIdProps i ]


mkStId :: Id -> Id -> Id
mkStId a b = join2ids a a fsDot b

mkNumId :: Integer -> Id
mkNumId i =
    if i < 0 then
        internalError ("mkNumId: " ++ show i)
    else
        Id noPosition fsEmpty (mkNumFString i) []

mkStrId :: FString -> Id
mkStrId s = Id noPosition fsEmpty s []

mkIdPre :: FString -> Id -> Id
mkIdPre fs a = setIdBase a (concatFString [fs, getIdBase a])

mkIdPost :: Id -> FString -> Id
mkIdPost a fs = setIdBase a (concatFString [getIdBase a, fs])

-- concatenate two Ids with the same package name (error if pkg names differ)
mkConcatId :: Id -> Id -> Id
mkConcatId a b
    | a_pkg /= b_pkg =
        internalError ("Id.mkConcatIds: " ++ show (getIdFStrings a) ++
                       " and " ++ show (getIdFStrings b))
    | otherwise = mkQId (getPosition a) a_pkg (concatFString [a_name, b_name])
    where (a_pkg, a_name) = getIdFStrings a
          (b_pkg, b_name) = getIdFStrings b

mkSplitId :: Id -> FString -> Id
mkSplitId idx fs = addIdProp (mkIdPost idx fs) IdPSplitRule

-- Mark an identifier as being generated internally
setInternal :: Id -> Id
setInternal i = addIdProp i IdPInternal

isInternal :: Id -> Bool
isInternal i = hasIdProp i IdPInternal

----
addIdSuffix :: Id -> Integer -> Id
addIdSuffix idx intx = mkIdPost idx (mkFString (show intx))

mkRdyId :: Id -> Id
mkRdyId i = addIdProp (mkIdPre fs_rdy i) IdPReady

isRdyId :: Id -> Bool
isRdyId idx = hasIdProp idx IdPReady

isKeepId :: Id -> Bool
isKeepId idx = hasIdProp idx IdP_keep

isHideId :: Id -> Bool
isHideId idx = hasIdProp idx IdP_hide

isHideAllId :: Id -> Bool
isHideAllId idx = hasIdProp idx IdP_hide_all

isDictId :: Id -> Bool
isDictId i = hasIdProp i IdPDict

isRuleId :: Id -> Bool
isRuleId idx = hasIdProp idx IdPRule

isBadId :: Id -> Bool
isBadId idx = hasIdProp idx IdP_bad_name

isFromRHSId :: Id -> Bool
isFromRHSId idx = hasIdProp idx IdP_from_rhs

isSplitRuleId :: Id -> Bool
isSplitRuleId idx = hasIdProp idx IdPSplitRule

isRenamingId :: Id -> Bool
isRenamingId idx = hasIdProp idx IdPRenaming

rmKeepId :: Id -> Id
rmKeepId idx = rmIdProp idx IdP_keep

setKeepId :: Id -> Id
setKeepId idx = addIdProp idx IdP_keep

rmHideId :: Id -> Id
rmHideId idx = rmIdProp idx IdP_hide

rmHideAllId :: Id -> Id
rmHideAllId idx = rmIdProp idx IdP_hide_all

setHideId :: Id -> Id
setHideId idx = addIdProp idx IdP_hide

setHideAllId :: Id -> Id
setHideAllId idx = addIdProp idx IdP_hide_all

setBadId :: Id -> Id
setBadId idx = addIdProp idx IdP_bad_name

setFromRHSId :: Id -> Id
setFromRHSId idx = addIdProp idx IdP_from_rhs

setSignedId :: Id -> Id
setSignedId a = addIdProp a IdP_signed

isSignedId :: Id -> Bool
isSignedId a = hasIdProp a IdP_signed

setNakedInstId :: Id -> Id
setNakedInstId a = addIdProp a IdP_NakedInst

isNakedInstId :: Id -> Bool
isNakedInstId a = hasIdProp a IdP_NakedInst

getIdDisplayName :: Id -> Maybe FString
getIdDisplayName idx =
    let names = nub [ name | (IdPDisplayName name) <- getIdProps idx]
        get_one [a] = Just a
        get_one [] = Nothing
        get_one _ = internalError $ "Id:getIdDisplayName " ++ (show_full idx)
    in get_one names

setIdDisplayName :: Id -> FString -> Id
setIdDisplayName idx name = addIdProp idx (IdPDisplayName name)

addIdDisplayName :: Id -> Id
addIdDisplayName i =
    case (getIdDisplayName i) of
      Nothing   -> i
      Just name -> setIdBase i name

getFromReady :: Id -> String
getFromReady idx =
        if ( isRdyId idx )
            then drop ((length . getFString) fs_rdy) tmp
            else tmp
    where tmp = getIdString idx

dropRulePrefixId :: Id -> Id
dropRulePrefixId idx
   | isRuleId idx = idx { id_fs = mkFString new_name }
   | otherwise = idx
       where new_name = drop ((length . getFString) fs_rl) (getIdString idx)

dropRulePrefix :: Id -> String
dropRulePrefix = getIdString . dropRulePrefixId

dropWillFirePrefixId :: Id -> Id
dropWillFirePrefixId idx
   | hasIdProp idx IdPWillFire = idx { id_fs = mkFString new_name }
   | otherwise                 = idx
  where new_name = drop ((length . getFString) fsWillFire) (getIdString idx)

dropWillFirePrefix :: Id -> String
dropWillFirePrefix = getIdString . dropWillFirePrefixId

dropCanFirePrefixId :: Id -> Id
dropCanFirePrefixId idx
   | hasIdProp idx IdPCanFire = idx { id_fs = mkFString new_name }
   | otherwise                 = idx
  where new_name = drop ((length . getFString) fsCanFire) (getIdString idx)

dropCanFirePrefix :: Id -> String
dropCanFirePrefix = getIdString . dropCanFirePrefixId

dropReadyPrefixId :: Id -> Id
dropReadyPrefixId idx
   | hasIdProp idx IdPReady = idx { id_fs = mkFString new_name }
   | otherwise                 = idx
  where new_name = drop ((length . getFString) fs_rdy) (getIdString idx)

mkEnableId :: Id -> Id
mkEnableId idx =
    addIdProp (mkIdPre fsEnable idx)  IdP_enable

getIdInlinedPositions :: Id -> Maybe [Position]
getIdInlinedPositions i =
    case [ poss | (IdPInlinedPositions poss) <- getIdProps i] of
      [] -> Nothing
      [poss] -> Just poss
      _ -> internalError("getIdInlinedPositions: " ++ show_full i)

addIdInlinedPositions :: Id -> [Position] -> Id
addIdInlinedPositions i [] = i
addIdInlinedPositions i new_poss =
    let isIdPInlinedPositions (IdPInlinedPositions _) = True
        isIdPInlinedPositions _ = False
        (inlinedpos_ps, other_ps) =
            partition isIdPInlinedPositions (getIdProps i)
        new_p =
            case inlinedpos_ps of
              [] -> IdPInlinedPositions new_poss
              [IdPInlinedPositions poss]
                 -> IdPInlinedPositions (new_poss ++ poss)
              _  -> internalError("addIdInlinedPosition: " ++ show_full i)
    in  setIdProps i (new_p : other_ps)

removeIdInlinedPositions :: Id -> Id
removeIdInlinedPositions i =
    let isIdPInlinedPositions (IdPInlinedPositions _) = True
        isIdPInlinedPositions _ = False
        other_ps = filter (not . isIdPInlinedPositions) (getIdProps i)
    in  setIdProps i other_ps

instance NFData Id where
    rnf a@(Id {}) = ()       -- XXX

-- #############################################################################
-- # Methods for adding properties to Id's, checking for them etc.
-- #############################################################################

addIdProp :: Id -> IdProp -> Id
addIdProp a prop = setIdProps a (union (getIdProps a) [prop])

rmIdProp :: Id -> IdProp -> Id
rmIdProp a prop = setIdProps a (delete prop (getIdProps a))

rmIdPropBy :: Id -> (IdProp -> Bool) -> Id
rmIdPropBy a predf = setIdProps a (filter predf (getIdProps a))

addIdProps :: Id -> [IdProp] -> Id
addIdProps a propl = setIdProps a (union (getIdProps a) propl)

hasIdProp :: Id -> IdProp -> Bool
hasIdProp a prop = elem prop (getIdProps a)

hasAnyIdProp :: Id -> [IdProp] -> Bool
hasAnyIdProp a props =  not $ null (intersect props (getIdProps a))

copyIdProps :: Id -> Id -> Id
copyIdProps src_id dst_id = addIdProps dst_id (getIdProps src_id)

-- #############################################################################
-- #
-- #############################################################################

isFire :: Id -> Bool
isFire i = hasAnyIdProp i [IdPCanFire, IdPWillFire]

mkIdCanFire :: Id -> Id
mkIdCanFire idx = addIdProp (mkIdPre fsCanFire idx) IdPCanFire

isIdCanFire :: Id -> Bool
isIdCanFire i = hasIdProp i IdPCanFire

mkIdWillFire :: Id -> Id
mkIdWillFire idx = addIdProp (mkIdPre fsWillFire idx) IdPWillFire

isIdWillFire :: Id -> Bool
isIdWillFire i = hasIdProp i IdPWillFire

isIdEnable :: Id -> Bool
isIdEnable i = hasIdProp i IdP_enable

mkIdTempReturn :: Bool -> Id -> Integer -> Id
mkIdTempReturn is_av idx n =
  let fn_type = if is_av then fsAVValue else fsMethodReturn
      raw = getIdBaseString idx
      --base = dropWhile (\c -> c `elem`  ['$','_'] ) raw
      base = if ( headOrErr "mkIdTempReturn" raw `elem`  ['$','_'] )
             then "Task_" ++ raw
             else raw
      new_name = concatFString [ mkFString base
                               , fsUnderUnder
                               , fn_type
                               , mkNumFString n
                               ]
  in setInternal (setIdBase idx new_name)

mkIdRule :: Id -> Id
mkIdRule i = addIdProp (mkIdPre fs_rl i) IdPRule

-- #############################################################################
-- #
-- #############################################################################

instance ToString Id where
    itos a = internalError "itos applied to Id " ++ show a
    to_string a = getIdString a

instance ToString [Id] where
    itos a = internalError "itos applied to [Id] " ++ show a
    to_string a = "[" ++ intercalate "," (map to_string a) ++ "]"

instance ToString (Id, Id) where
    itos a = internalError "itos applied to (a) " ++ show a
    to_string (a, b) = "(" ++ to_string a ++ "," ++ to_string b ++ ")"

----------------------------
type IdMap = Map.Map Id Integer

-- given a list of already used ids, and a list of potentially
--conflicting id, generate a list of non-conflicting ids, and map to
--rename ids.
genUniqueIdsAndMap :: [Id] -> [Id] -> ([Id], [(Id,Id)])
genUniqueIdsAndMap usedIds newIds = (safeIds, changeMap)
    where
     usedMap :: IdMap
     usedMap  = Map.fromList $ zip usedIds (repeat 0)
     (_, safeIds, changeMap) = foldl checkNewIds (usedMap,[],[]) newIds
     checkNewIds :: ( IdMap, [Id], [(Id,Id)] ) -> Id -> ( IdMap, [Id], [(Id,Id)] )
     checkNewIds (idmap, safeids, transmap) checkid = (idmap', safeids', transmap')
         where
         (rootid,suffix) = stripId_Suffix checkid
         (idmap', safeids', transmap') = if (checkid `Map.member` idmap) then
                                         let
                                         (newerid,newmap) = genNewId rootid idmap
                                         in ( newmap,
                                              newerid : safeids,
                                              (checkid,newerid):transmap
                                            )
                                         else
                                         ( (Map.insert checkid suffix idmap),
                                           checkid: safeids,
                                           transmap
                                         )

-- strip out the suffix from an Id returning the base, and the Integer
-- suffix.  The Id must be flagged with IdP_suffixed.
stripId_Suffix :: Id -> (Id,Integer)
stripId_Suffix idin = idout
    where
    idout = if (idin `hasIdProp` IdP_suffixed) then
            -- strip the suffix off the name
            let idstr =  getIdString idin
                unders = elemIndices '_' idstr
                under = lastOrErr ("Name within Id does not match suffix attribute: " ++ show idin) unders
                root  = take under idstr
                suff = drop (under+1) idstr
                ints = map ( toInteger . digitToInt) suff
                tenx i j = (10 * i) + j
                base = foldl1 tenx ints
            in ( rmIdProp (setIdBase idin (mkFString root)) IdP_suffixed,  base )
            else (idin,0)

-- add an underscore suffix to the ids, and the flag that it has been added.   Do not add more than 1 suffix!
addId_Suffix :: Id -> Integer -> Id
addId_Suffix idx intx = addId_SuffixPadded idx intx 0

-- the same, allowing multiple suffixes.
addId_Suffixes :: Id -> Integer -> Id
addId_Suffixes idx intx = mkIdPost idx (mkFString ("_" ++ (show intx)))

addId_SuffixPadded :: Id -> Integer -> Integer ->Id
addId_SuffixPadded idx intx chars = newId
    where
    newId = if ( idx `hasIdProp` IdP_suffixed )
            then internalError("addId_Suffix: suffix already exists: " ++ show idx )
            else withProp
    withProp = addIdProp id1 IdP_suffixed
    -- insure that the id has a name ! WTF
    givename = if ( isEmptyId idx ) then setIdBase idx fs_unnamed else idx
    id1      = mkIdPost givename (mkFString ("_" ++ (addZeros (show intx) chars)))


addZeros :: String -> Integer -> String
addZeros digitString size =
    if (size > (toInteger (length digitString)))
    then "0" ++ (addZeros digitString (size - 1))
    else digitString

-- #############################################################################
-- # Yet another flavor of "add suffix" that allows multiple suffixes.
-- #############################################################################

addSuffix :: Id -> Integer -> Id
addSuffix idx n =
    let count = getSuffixCount idx
        id_init = if (isEmptyId idx) then setIdBase idx fs_unnamed else idx
        keep_prop prop = not (isSuffixCountProp prop)
        id_clean = rmIdPropBy id_init keep_prop
        id_suffixed = mkIdPost (addIdProp id_clean (IdP_SuffixCount (count + 1))) (mkFString ("_" ++ (show n)))
        out = if (hasIdProp id_suffixed IdP_suffixed)
                then internalError("Id:addSuffix: Inconsistent use of suffix forms: " ++ show idx)
                else id_suffixed
    in out

isSuffixCountProp :: IdProp -> Bool
isSuffixCountProp (IdP_SuffixCount _) = True
isSuffixCountProp _ = False

getSuffixCount :: Id -> Integer
getSuffixCount idx =
    let count_list = nub [ count | (IdP_SuffixCount count) <- getIdProps idx]
        get_count [a] = a
        get_count [] = 0
        get_count _ = internalError "Id:getSuffixCount"
    in get_count count_list

removeSuffix :: Id -> (Id, Integer)
removeSuffix idx =
    let count = getSuffixCount idx
        keep_prop prop = not (isSuffixCountProp prop)
        id_clean = rmIdPropBy idx keep_prop
        out | hasIdProp id_clean IdP_suffixed
                = internalError("Id:removeSuffix: Inconsistent use of suffix forms: " ++ show idx)
            | count == 0
                = internalError("Id:removeSuffix: Id has no suffix: " ++ show idx)
            | otherwise
                = let (fstring, suffix) = removeFStringSuffix (getIdBase id_clean)
                  in  ((addIdProp (setIdBase id_clean fstring) (IdP_SuffixCount (count - 1))), suffix)
    in out

removeFStringSuffix :: FString -> (FString, Integer)
removeFStringSuffix fstring =
    let string = getFString fstring
        unders = elemIndices '_' string
        under = lastOrErr ("Name does not have a suffix: " ++ show string) unders
        root  = take under string
        suff = drop (under+1) string
        ints = map ( toInteger . digitToInt) suff
        tenx i j = (10 * i) + j
        base = foldl1 tenx ints
    in (mkFString root ,base)

removeAllSuffixes :: Id -> Id
removeAllSuffixes idx =
    let count = getSuffixCount idx
        (idx', _) = removeSuffix idx
    in if (count > 0) then removeAllSuffixes idx' else idx

-- #############################################################################
-- #
-- #############################################################################

-- generate a new id with a numerical suffix, based in the original id  The new id will not be in
-- the IdMap, but will be added, along with an update of the max suffix
genNewId :: Id -> IdMap -> ( Id, IdMap )
genNewId origId idmap =  (newid, newMap)
    where
    (rootid,suffix) = stripId_Suffix origId
    (newid,newsuff) = tryThisId rootid (suffix + 1)
    newMap = Map.insert newid newsuff (Map.insert rootid newsuff idmap)
    tryThisId :: Id -> Integer -> (Id,Integer)
    tryThisId baseId suff =
        let
        genId = addId_Suffix baseId suff
        in if (genId `Map.member` idmap)
           then tryThisId baseId (suff+1)
           else (genId,suff)

-- Add a path string to an existing Id's qualified path
-- This is used during the Bluesim backend, when Id qualifiers
-- hold instance path information.  It should not be used
-- with the module qualifiers used in the rest of the compiler.
addToQual :: String -> Id -> Id
addToQual prefix a =
  let fsPrefix = mkFString prefix
      fsQual   = getIdQual a
      fsQual' | fsQual == fsEmpty   = fsPrefix
              | fsPrefix == fsEmpty = fsQual
              | otherwise           = concatFString [fsPrefix, fsDot, fsQual]
  in setIdQual a fsQual'


-- This is used in ASchedule, to qualify rules from submodules with their
-- instance name.  Unlike "addToQual" in the Bluesim backend, the base is
-- the name that is important (the qualifier, if it exists at all, might
-- be a package name; and place which print rule Ids probably use
-- "getIdBaseString", and if they used "pfpString" they'd print the
-- qualifier with "::" and not ".").
addToBase :: Id -> Id -> Id
addToBase prefix a =
  let fsPrefix = getIdBase prefix
      fsBase   = getIdBase a
      fsBase'  = if (fsPrefix == fsEmpty)
                 then fsBase
                 else concatFString [fsPrefix, fsDot, fsBase]
  in setIdBase a fsBase'
