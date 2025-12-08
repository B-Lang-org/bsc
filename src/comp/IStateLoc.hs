{-# LANGUAGE DeriveDataTypeable #-}
module IStateLoc (
  IStateLoc
  ,IStateLocPathComponent(..)
  ,StateLocMap
  ,isLoop
  ,isAddRules
  ,stateLocToHierName
  ,stateLocToPrefix
  ,stateLocToId
  ,stateLocAndNameToRuleId
  ,addStateLocToPragmaRuleId
  ,createSuffixedId
  ,hasIgnore
  ,hasHide
  ,hasHideAll
  ,extendStateLocMap
  ,newIStateLocTop
  ) where

import IType
import Id
import qualified Data.Generics as Generic
import Eval
import Data.Char(isAlphaNum)

import Position
import PreStrings(fsUnderscore,fsElements, fsvElements)
import FStringCompat
import PPrint
import PFPrint(pfpString)
import PreStrings(fs_unnamed, fsAddRules, fsLoop, fsBody, fsC)
import qualified Data.Map as M
import Data.List(isPrefixOf,tails)
import Error(internalError)
import IOUtil(progArgs)
import Util(traces)



-- Debug
doTraceLoc :: Bool
doTraceLoc = elem "-trace-state-loc" progArgs


-- ==============================
-- IStateLoc is a list of path components.  Lowest level of hierarchy is at the head.
type IStateLoc = [IStateLocPathComponent]


-- path to a location in the instantiation hierarchy
-- i.e., names/types of variables bound on the path to this instantiation
--   * nearest enclosing bind comes first
-- e.g., [_r, r, component, toplevel, _y] for a register r inside component
--       instantiated inside toplevel

data IStateLocPathComponent = IStateLocPathComponent {
  isl_inst_id                 :: Id, -- instance id (from SV instantiation or <- syntax)
  isl_ifc_id                 :: Id, -- interface id (used in source code to access module)
  isl_ifc_type                 :: IType, -- interface type

  -- Some flags
  isl_vector                :: Bool, -- Is a vector name
  isl_inst_ignore         :: Bool, -- inslpc may be eliminated from the istateloc.
  isl_inst_ignore_name         :: Bool, -- inst_id is ignored when making a hierarchical name
  isl_ifc_skip          :: Bool, -- skip this level in the rule name scope lookup

  -- Unique index to uniquify InstTree (loops, common names)
  isl_unique_index         :: Maybe Integer, -- nothing if not unique, otherwise disambiguating integer

  -- Name generation
  isl_prefix                 :: NameGenerate, -- currently computed hierarchical prefix
  isl_loop_suffix         :: NameGenerate  -- loop indexes to add once a "real" name is found.
  } deriving (Eq, Show, Generic.Data, Generic.Typeable)


-- ---------------------------------------
instance NFData IStateLocPathComponent where
  rnf (IStateLocPathComponent a b c d e f g h i j) = rnf10 a b c d e f g h i j

-- ---------------------------------------
instance HasPosition IStateLocPathComponent where
  getPosition = getPosition . isl_prefix

-- ---------------------------------------
-- for debug ONLY
instance PPrint IStateLocPathComponent where
    pPrint d p islpc = pPrint d p ((id1, id2), (uniqified, ignore, vector, skip), (prefix,lp), t)
                          -- <> text (getIdProps id1)
                          -- <> text (show_full id1)
      where id1       = isl_inst_id  islpc
            id2       = isl_ifc_id   islpc
            t         = isl_ifc_type islpc
            uniqified = isl_unique_index islpc
            ignore    = toTF $ isl_inst_ignore islpc
            vector    = toTF $ isl_vector islpc
            skip      = toTF $ isl_ifc_skip islpc
            prefix    = isl_prefix islpc
            lp        = isl_loop_suffix islpc


-- Common constructor
mkISLPC :: Id -> Id -> IType -> IStateLocPathComponent
mkISLPC inst_id ifc_id ifc_type = islpc
  where ignore_name = ignoreInstIdName inst_id
        ignore = ignoreInstId inst_id
        --
        islpc = IStateLocPathComponent {
          isl_inst_id          = inst_id,
          isl_ifc_id           = ifc_id,
          isl_ifc_type         = ifc_type,
          isl_inst_ignore      = ignore,
          isl_inst_ignore_name = ignore_name,
          isl_ifc_skip         = False,
          isl_vector           = False,
          isl_unique_index     = Nothing,
          isl_prefix           = NameEmpty,
          isl_loop_suffix      = NameEmpty
          }


-- ---------------------------------------------------------
-- Utility structure used in name generation
data NameGenerate = NameEmpty             -- No name so far
                    | NameIndex [Integer] -- loop indexes
                    | Name Id             -- a real name
                    deriving (Eq, Show, Generic.Data, Generic.Typeable)

--
instance NFData NameGenerate where
  rnf (NameEmpty)    = rnf ()
  rnf (NameIndex is) = rnf is
  rnf (Name n)       = rnf n

--
instance HasPosition NameGenerate where
  getPosition (Name n) = getPosition n
  getPosition _        = noPosition

instance PPrint NameGenerate where
  pPrint d p (Name n)       = pPrint d p n
  pPrint d p (NameIndex is) = pparen True (text "NameIndex" <+> pPrint d p is)
  pPrint d p (NameEmpty)    = text "NameEmpty"

--
-- Join 2 names together
-- indexes always go on the end of the name
-- names are joined with underscore
joinNames :: NameGenerate -> NameGenerate -> NameGenerate
joinNames NameEmpty x                                 = x
joinNames x NameEmpty                                 = x
joinNames (NameIndex n1) (NameIndex n2)         = NameIndex $ n1 ++ n2
joinNames (Name n)  (NameIndex idxs)                   = Name $ foldl addId_Suffixes n idxs
joinNames n1@(NameIndex {}) n2@(Name {})         = joinNames n2 n1
joinNames (Name n1) (Name n2)                         = Name $ mkIdPre head_ n2
  where head_ = concatFString [getIdBase n1, fsUnderscore]

-- The name when none is present
noName :: NameGenerate
noName = Name $ mkId noPosition $ _unnamed_
    where _unnamed_ = concatFString [fsUnderscore, fs_unnamed, fsUnderscore]

-- Generate an Id
toStateName :: NameGenerate -> Id
toStateName NameEmpty        = toStateName noName
toStateName (Name n)         = n
toStateName x@(NameIndex {}) = toStateName $ joinNames noName x

-- create a friendly name for code generation
-- Bool arg is ignore
cleanName :: Bool -> Id -> NameGenerate
cleanName ignore i | ignore = NameEmpty
                   | otherwise = Name $ cleanupInstId i

-- Generate possible NameIndex
-- Bool argument is use
indexName :: Bool -> Maybe Integer -> NameGenerate
indexName True (Just i) = NameIndex [i]
indexName _ _           = NameEmpty


-- ---------------------------------------
-- ---------------------------------------
-- Entry point for generating a state loc at this level
newIStateLocTop :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLocTop slmap inst_id ifc_id ifc_type [] = [comp]
  -- first entry in the hierarchy
  where comp = IStateLocPathComponent {
            isl_inst_id          = inst_id,
            isl_ifc_id           = ifc_id,
            isl_ifc_type         = ifc_type,
            isl_inst_ignore      = ignore,
            isl_inst_ignore_name = ignore_name,
            isl_ifc_skip         = False,
            isl_vector           = False,
            isl_unique_index     = Nothing,
            isl_prefix           = cleanName ignore_name inst_id,
            isl_loop_suffix          = NameEmpty
            }
        ignore = ignoreInstId inst_id
        ignore_name = ignoreInstIdName inst_id


newIStateLocTop slmap inst_id ifc_id ifc_type parent@(head_loc:_) = trid $ fchild slmap inst_id ifc_id ifc_type parent
  where new_vector =  isVectorName inst_id
        element    =  isElementName inst_id
        same_ifc   =  ifc_type == (isl_ifc_type head_loc)
        parentIsLoop = isLoop parent
        parentIsVector = isVector parent
        same_pos   = (getPosition inst_id) == (getPosition (isl_inst_id head_loc))
        same_namloc = same_pos && same_ifc
        --
        -- determine proper type for this instance
        -- --
        (name,fchild) = case (new_vector, element, parentIsVector, same_ifc, same_namloc, parentIsLoop) of
          (True , _,    _,     _,    _,    _    ) -> ("vector0",newIStateLoc_newVectorElem)
          (False, True, True,  True, _    , _   ) -> ("vectorN",newIStateLoc_nextVectorElem)
          (False, True, False, True, False, _   ) -> ("listElem",newIStateLoc_recursiveElem)
          (_,     _,    _,     _,    _,     True) -> ("loop",newIStateLoc_loop)
          (_,     _,    _,     _,    _,     _   ) -> ("other",newIStateLoc_other)
          --
        trid = if (doTraceLoc) then tr else id
        tr = traces ("IStateloc " ++ name ++ ": " ++ ppReadable
                     (inst_id,(map toTF [new_vector, element, parentIsVector, same_ifc, same_namloc, parentIsLoop]))
                     ++ ppReadable (map isl_inst_id (take 3 parent) )
                     )



-- If we have a vector, give it an index of 0
-- vector determined by "_velement" name given in Vector.bs
newIStateLoc_newVectorElem :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLoc_newVectorElem slmap inst_id ifc_id ifc_type parent = (islpc':parent)
  where idx = Just 0
        --
        islpc = mkISLPC inst_id ifc_id ifc_type
        islpc' = islpc {
          isl_vector           = True,
          isl_unique_index     = idx,
          isl_ifc_skip         = True, -- Skip in rule name lookup
          isl_prefix           = (currentName parent) `joinNames`
                                 indexName True idx
          }

-- Vectors are instantiation recursively in List::mapM
-- Increment the index from the parent and then relace parent
newIStateLoc_nextVectorElem :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLoc_nextVectorElem slmap inst_id ifc_id ifc_type parent@(head_loc:rest) = (islpc':rest)
  where idx = Just $ incrMaybe $ isl_unique_index head_loc
        --
        ignore_name = ignoreInstIdName inst_id
        new_id_info = cleanName ignore_name inst_id
        islpc = mkISLPC inst_id ifc_id ifc_type
        islpc' =  islpc {
          isl_vector           = True,
          isl_unique_index     = idx,
          isl_ifc_skip         = True, -- Skip in rule name lookup
          isl_prefix           = foldl1 joinNames [(currentName rest),
                                                   new_id_info,
                                                   indexName True idx]
          }

newIStateLoc_nextVectorElem slmap inst_id ifc_id ifc_type [] =
  internalError $ "newIStateLoc_nextVectorElem"

-- We are skipping the "_elements" entry here, the next level down will be uniquified
-- e.g. _element
newIStateLoc_recursiveElem :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLoc_recursiveElem  slmap inst_id ifc_id ifc_type parent@(head_loc:rest) = parent
newIStateLoc_recursiveElem  slmap inst_id ifc_id ifc_type [] =
  internalError $ "newIStateLoc_recursiveElem"

-- This is the body of a loop, that is, the parent was a "loop"
-- We'll add an entry and make sure it is unique w.r.t. index
newIStateLoc_loop :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLoc_loop  slmap inst_id ifc_id ifc_type parent@(head_loc:_) = isl'
  where ignore_name = ignoreInstIdName inst_id
        -- Set the name to "Body" unless it has a usable names  e.g. single bind in a loop
        inst_id' = if (ignore_name) && (getIdDisplayName inst_id == Nothing) then setIdDisplayName inst_id fsBody else inst_id
        --
        islpc = (mkISLPC inst_id' ifc_id ifc_type) {
          isl_inst_ignore      = False, -- DO not ignore
          isl_inst_ignore_name = False,
          isl_ifc_skip         = True -- Skip in rule name lookup
          }
        isl = (islpc:parent)
        --
        -- Check the index for the loop
        uniq :: Maybe Integer
        uniq = M.lookup (createStateLocMapKey isl) slmap
        -- The map contains the next index to use
        -- For Loops we convert Nothing to 0
        nextIdx = maybe 0 id uniq
        -- The next suffix or maybe use it now
        suffix = (isl_loop_suffix head_loc) `joinNames` (NameIndex [nextIdx])
        vectorbind = isPrefixOf (getFString fsC) (getIdBaseString ifc_id)
        --
        -- If there is a good name, then use it, adding loop indices
        (new_prefix, new_suffix, new_uniq) = case (ignore_name, vectorbind) of
          -- pass the name and add index to the suffix
          (True, _)      -> ((isl_prefix head_loc)  ,suffix, Just nextIdx)
          -- New names
          (False, False) -> let goodname = foldl1 joinNames [isl_prefix head_loc,
                                                             (cleanName False inst_id),
                                                             suffix]
                            in (goodname ,NameEmpty, Just nextIdx)
          (False, True)  -> let goodName =  foldl1 joinNames [isl_prefix head_loc,
                                                              (cleanName False inst_id) ]
                            in (goodName, NameEmpty, Nothing)
        --
        islpc' = islpc { isl_unique_index = new_uniq,
                         isl_prefix = new_prefix,
                         isl_loop_suffix = new_suffix
                       }
        isl' = (islpc':parent)

newIStateLoc_loop  slmap inst_id ifc_id ifc_type [] = internalError "newIStateLoc_loop"

-- The default case.   Add the instance to hierarchy, add unique index if needed.
newIStateLoc_other :: StateLocMap -> Id -> Id -> IType -> IStateLoc -> IStateLoc
newIStateLoc_other  slmap inst_id ifc_id ifc_type parent@(head_loc:_rest) = isl'
  where ignore_name = ignoreInstIdName inst_id
        new_id_info = cleanName ignore_name inst_id
        --
        -- This is abit of a hack.  the front end nicely desugars
        -- foo[i] <- mkFoo to a good name,  So we do not want to add
        -- our naming here.
        vectorbind = (not ignore_name) && (isPrefixOf (getFString fsC) (getIdBaseString ifc_id))
        (loop_suffix,new_id_info') = case (vectorbind, new_id_info) of
          (True,  x         ) -> (NameEmpty, x)
          (False, x@(Name i)) -> (NameEmpty, joinNames x $ isl_loop_suffix head_loc)
          (False, x         ) -> (isl_loop_suffix head_loc, x)
        --
        isl0 = mkISLPC inst_id ifc_id ifc_type
        islpc = isl0 {
          -- Copy the unique index down for vectors
          isl_unique_index     = if (isl_vector head_loc) then (isl_unique_index head_loc) else Nothing,
          isl_prefix           = (isl_prefix head_loc) `joinNames` new_id_info',
          isl_loop_suffix      = loop_suffix
          }
        isl = (islpc:parent)
        -- Check that the create key is unique
        uniq :: Maybe Integer
        uniq = M.lookup (createStateLocMapKey isl) slmap
        -- The map contains the next index to use or Nothing
        isl' = updateUniqIdx uniq isl

newIStateLoc_other _ _ _ _ [] = internalError "newIStateLoc_other"


-- ---------------------------------------
-- Utility functions

-- convert a list of hierarchical locations to a full Id (for instances)
-- empty hierarchy will get the name "_unnamed_"
stateLocToId :: IStateLoc -> Id
stateLocToId (x:_) = toStateName $ isl_prefix x
stateLocToId _ = toStateName noName

hasIgnore :: IStateLoc -> Bool
hasIgnore [] = False
hasIgnore (head_loc : _ ) =
    (isl_inst_ignore head_loc) || (isl_ifc_skip head_loc)

hasHide :: IStateLoc -> Bool
hasHide [] = False
hasHide (head_loc : _) = isHideId (isl_inst_id head_loc)

hasHideAll :: IStateLoc -> Bool
hasHideAll locs = any (isHideAllId . isl_inst_id) locs

isAddRules :: IStateLoc -> Bool
isAddRules [] = False
isAddRules (head_loc : _) =
    (getIdDisplayName (isl_inst_id head_loc) == Just fsAddRules)

isLoop :: IStateLoc -> Bool
isLoop [] = False
isLoop (head_loc : _) =
    (getIdDisplayName (isl_inst_id head_loc) == Just fsLoop)

isVector :: IStateLoc -> Bool
isVector [] = False
isVector (head_loc : _) = isl_vector head_loc

currentName :: IStateLoc -> NameGenerate
currentName [] = NameEmpty
currentName (h:_) = isl_prefix h

ignoreInstIdName :: Id -> Bool
ignoreInstIdName i = (idUnderscoreDepth i > 0)

--
-- Do not ignore _ names with keep flag
ignoreInstId :: Id -> Bool
ignoreInstId id | (idUnderscoreDepth id > 1)                        = True
ignoreInstId id | (not (isKeepId id)) && (idUnderscoreDepth id > 0) = True
ignoreInstId _                                                      = False

-- count the number of underscores at the start of an Id
idUnderscoreDepth :: Id -> Integer
idUnderscoreDepth = underscoreDepth . getIdString

-- count the number of underscores at the start of a string
underscoreDepth :: String -> Integer
underscoreDepth ('_':s) = 1 + underscoreDepth s
underscoreDepth _       = 0



-- ---------------------------------------
-- filter out illegal characters and
-- drop all Id properties
-- (so they don't cause problems downstream)
cleanupInstId :: Id -> Id
cleanupInstId i = mkId pos fstr
  where fstr = mkFString str_filtered
        str_filtered = filter legalChar (getIdString i)
        legalChar c = isAlphaNum c || c == '_'
        pos = getIdPosition i

-- Add an integer suffix to an Id, unless it is 0
createSuffixedId :: Id -> Integer -> Id
createSuffixedId id no =
    if (no == 0)
    then id
    else (addSuffix id (toInteger no))

-- convert a list of hierarchical locations to a prefix (for rules/methods)
-- the prefix will end in _
stateLocToPrefix :: IStateLoc -> Id
stateLocToPrefix [] = emptyId
stateLocToPrefix (h:_) = case (isl_prefix h) of
  Name i       -> mkIdPost i fsUnderscore
  NameIndex xs -> emptyId
  NameEmpty    -> emptyId


-- a "." separated name of the hier path,  used for -show-elab-progress
stateLocToHierName :: IStateLoc -> Bool -> Maybe String
stateLocToHierName locs showHidden =
    let
        getNameString i =
          case (getIdDisplayName i) of
            Nothing -> pfpString i
            Just fstr -> getFString fstr

        addToName Nothing  i = Just $ (getNameString i)
        addToName (Just s) i = Just $ (getNameString i) ++ "." ++ s

        -- this replicates the check in "hasIgnore"
        foldFn m loc | (isl_inst_ignore loc || isl_ifc_skip loc) = m
        foldFn m loc | showHidden = addToName m (isl_inst_id loc)
        foldFn m loc | isHideAllId (isl_inst_id loc) = Nothing
        foldFn m loc | isHideId (isl_inst_id loc) = m
        foldFn m loc = addToName m (isl_inst_id loc)
    in
        foldl foldFn Nothing locs


-- ----------

-- This function used to take just the "ns" (the module hierarchy
-- for this rule, potentially empty if the rules is at the top-level)
-- and a position and would make an Id.  Then it was up to the
-- function "cleanupFinalRules" to later append the rule's name
-- and anything necessary to uniquify the rulename.  Now, we go ahead
-- and append the rule name here, and only uniquify later.
stateLocAndNameToRuleId :: IStateLoc -> String -> Position -> Id
stateLocAndNameToRuleId ns str pos = id
 where id = setIdPosition pos (mkIdPost (stateLocToPrefix ns) (mkFString str))

addStateLocToPragmaRuleId :: IStateLoc -> Id -> Id
addStateLocToPragmaRuleId ns i = id
 where pos = getPosition i
       (_, id_fstr) = getIdFStrings i
       id = setIdPosition pos (mkIdPost (stateLocToPrefix ns) id_fstr)


-- extract the value and increment  1-based
incrMaybe :: Maybe Integer -> Integer
incrMaybe Nothing  = 1
incrMaybe (Just i) = (i+1)

-- Update the istateloc unique index and suffix
-- For hidden entries on the unique_index is updated, as we do not
-- want hidden layes adding the name suffix.
updateUniqIdx :: Maybe Integer -> IStateLoc -> IStateLoc
updateUniqIdx Nothing x        = x
updateUniqIdx _ []             = []
updateUniqIdx x@(Just i) (h:r) | isl_inst_ignore h = (h1 : r)
                               | otherwise         = (h2 : r)
    where
          h1 = h {isl_unique_index = x} -- only the uniq idx
          pre =  (isl_prefix h) `joinNames` ( isl_loop_suffix h) `joinNames` (indexName True x)
          h2 = h1 {isl_loop_suffix = NameEmpty,
                   isl_prefix = pre} -- add the suffix if the name is not empty....

----------------------
isVectorName :: Id -> Bool
isVectorName i = (fsvElements == (getIdFString $ unQualId i))


isElementName :: Id -> Bool
isElementName i = (fsElements == (getIdFString $ unQualId i))

-- ------------------------------------------------------
-- State Loc Map
-- This is used to obtain unique indexes for entries along the hierarchy/instanace tree
-- key is the path (inst name and possible unique int)
-- data is the next unique index.
type StateLocMap = M.Map [(Id, Maybe Integer)] Integer

-- given a stateloc path, generate a key for the statelocmap
-- the head always has Nothing as its key, the head is never ignored.
-- Keeping hidden head entries allosing unique tree nodes for hidden name
-- such as those generated in moduleContext.
createStateLocMapKey :: IStateLoc -> [(Id, Maybe Integer)]
createStateLocMapKey [] = internalError "createStateLocMapKey"
createStateLocMapKey (head:rest) = headkey:restkeys
    where headkey = (isl_inst_id head, Nothing)
          restkeys = [(isl_inst_id x, isl_unique_index x) | x <- rest, (not . isl_inst_ignore) x]

-- update the StateLocMap with new entries for all sub-hierarchies on the
-- along the current path
extendStateLocMap :: StateLocMap -> IStateLoc -> StateLocMap
extendStateLocMap slmap ns = foldl addPath slmap paths
    where paths :: [IStateLoc] -- all possible paths 2
          paths = init $ tails $ ns
          addPath :: StateLocMap -> IStateLoc -> StateLocMap
          addPath m isl = M.insert key nextIdx m
            where key = createStateLocMapKey isl
                  nextIdx = (incrMaybe . isl_unique_index . head) isl
