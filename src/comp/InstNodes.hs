{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module InstNodes(
    InstNode(..), InstTree,
    mkInstTree, getIStateLocs, flattenInstTree,
    isHidden, isHiddenKP, isHiddenAll, nodeChildren, comparein
  ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.Function(on)
import Data.List(sortBy,groupBy,isPrefixOf)
import qualified Data.Map as M
import Data.Ord(comparing)
import Control.Monad.State

import Util(mapSnd)
import Util(toMaybe)
import Eval
import ErrorUtil(internalError)
import PreStrings(fsBody)
import FStringCompat(getFString)
import PPrint
import Position(getPosition)
import Id
import GenWrapUtils(isGenId)
import CType
import ISyntax
import IStateLoc(IStateLoc, IStateLocPathComponent(..))

import IOUtil(progArgs)
import Debug.Trace

doTraceTree :: Bool
doTraceTree = elem "-trace-inst-tree" progArgs

-- -----------------------------------------------------------

type InstTree = M.Map Id InstNode

data InstNode = StateVar { node_name :: Id } |
                Rule   { node_name :: Id } |
                Loc    { node_name :: Id,
                         node_type :: Maybe CType,
                         node_ignore :: Bool,
                         node_ignore_name :: Bool,
                         uniquified :: Bool,
                         node_children :: InstTree }
  deriving(Eq, Show)

instance Ord InstNode where
  compare n1 n2 = cmpIdByName (node_name n1) (node_name n2)

instance NFData InstNode where
  rnf (StateVar name) = rnf name
  rnf (Rule name) = rnf name
  rnf (Loc name typ ign ignname uniq children) =
    rnf6 name typ ign ignname uniq children

instance PPrint InstNode where
  pPrint d p (StateVar i ) | isHideId i = text "StateVar (H) " <> pPrint d p i
  pPrint d p (StateVar i ) | isHideAllId i = text "StateVar (HA) " <> pPrint d p i
  pPrint d p (StateVar i ) = text "StateVar " <> pPrint d p i
  pPrint d p (Rule i) | isHideId i = text "Rule (H) " <> pPrint d p i
  pPrint d p (Rule i) | isHideAllId i = text "Rule (HA) " <> pPrint d p i
  pPrint d p (Rule i) = text "Rule " <> pPrint d p i
  pPrint d p (Loc n ct ig ign un children) | isHideId n = text "[Loc (H) " <> pPrint d p n <+> pPrint d p ig <+> pPrint d p (getIdDisplayName n)
                                            -- <+> pPrint d p (M.keys children)
                                            -- <+> pparen True (pPrint d p ct)
                                            $+$ (pPrint d p children)
                                            <+> (text "]")
  pPrint d p (Loc n ct ig ign un children) | isHideAllId n = text "[Loc (HA) " <> pPrint d p n <+> pPrint d p ig <+> pPrint d p (getIdDisplayName n)
                                            -- <+> pparen True (pPrint d p ct)
                                            $+$ (pPrint d p children)
                                           <+> (text "]")
  pPrint d p (Loc n ct ig ign un children) = text "[Loc " <> pPrint d p n <+> pPrint d p ig <+> pPrint d p (getIdDisplayName n)
                                            -- <+> pPrint d p (M.keys children)
                                            -- <+> pparen True (pPrint d p ct)
                                            $+$ (pPrint d p children) <+> (text "]")

-- we need to know if the name is ignored
-- AND if the hierarchy location is ignored (they are different)
-- This type mirrors the IStateLoc struct, and is used internally in the generation
-- of InstTrees
-- first Bool is hide attribute,  2nd is ignore name
type InstLoc = (Id, CType, Maybe Integer, Bool, Bool)

-- -----------------------------------------------------------
-- flattenInstNode and flattenInstTree are used in bsc.hs as an internal check
-- when the flag -hack-strict-inst-tree is set!
flattenInstNode :: InstNode -> [(Id, [(Id, Maybe CType)])]
flattenInstNode (StateVar i) = [(i, [])]
flattenInstNode (Rule i) = [(i, [])]
flattenInstNode (Loc i ct _ _ _ children) = mapSnd ((:) (i, ct)) (flattenInstTree children)

flattenInstTree :: M.Map k InstNode -> [(Id, [(Id, Maybe CType)])]
flattenInstTree tree = concatMap flattenInstNode (M.elems tree)

-- -----------------------------------------------------------
-- Trees with 1 child and an ignore flag are reduced
compressIgnoredChildren :: InstTree -> InstTree
compressIgnoredChildren tree = cs
  where
    cs = case (M.assocs tree) of
          [(_, l@(Loc {}))] | node_ignore l -> compressIgnoredChildren (node_children l)
          xs -> process  xs
    --
    -- Main merge function
    process = (M.fromList .
               (concatMap uniqGroup) .
               (groupBy ((==) `on` (node_name . snd))) .
               (sortBy (comparein `on` snd)) .
               (map removeSingletonBodies) .
               (concatMap uniqGroup) .
               (groupBy ((==) `on` (node_name . snd))) .
               (sortBy (comparein `on` snd)) .
               (concatMap promoteChildren) .
               (mapSnd compressIgnoredChildrenNode))
    --
    -- Compress the child nodes
    compressIgnoredChildrenNode :: InstNode -> InstNode
    compressIgnoredChildrenNode l1@(Loc { node_children = children }) =
      l1 { node_children = compressIgnoredChildren children }
    compressIgnoredChildrenNode n = n
    --
    -- promote children of Loc with ignore attribute
    promoteChildren :: (Id,InstNode) -> [(Id,InstNode)]
    promoteChildren (x, l@(Loc {})) | node_ignore l, isBadId x = M.toList $ node_children l
    promoteChildren x = [x]
    --
    -- after groupBy add numeric suffix for any Loc names which are the same
    uniqGroup :: [(Id,InstNode)] -> [(Id,InstNode)]
    uniqGroup []    = []
    uniqGroup [x]   = [x]
    uniqGroup xs    = (zipWith addSuffixII xs [0..])
    --
    addSuffixII :: (Id,InstNode) -> Integer -> (Id,InstNode)
    addSuffixII (id,l@(Loc {node_name = n})) idx = (n',l { node_name = n', uniquified = True })
        where n' = addSuffix n idx
    addSuffixII l _ = l
    --
    removeSingletonBodies ::  (Id,InstNode) -> (Id,InstNode)
    removeSingletonBodies (id,l@(Loc {node_name = n,
                                     node_children = x })) | isBodyName n, (M.size x) == 1 = head $ M.toList x
      where isBodyName :: Id -> Bool
            isBodyName i = isPrefixOf (getFString fsBody) (getIdBaseString i)
    removeSingletonBodies xs = xs

-- -----------------------------------------------------------

mkNodeTree :: InstNode -> InstTree
mkNodeTree n = M.singleton (node_name n) n

mkSingleTree :: InstNode -> [InstLoc] -> InstTree
mkSingleTree n [] = mkNodeTree n

mkSingleTree node locs@((name,ty,Nothing,ign,ign_name):rest) =  mkSingleTree node' rest
  where node' = Loc name (Just ty) ign ign_name False child
        child = M.singleton (node_name node) node

mkSingleTree node ((name,ty,Just i,ign,ign_name):rest) = mkSingleTree node' rest
  where num_name = addSuffix name i
        node' = Loc num_name (Just ty) ign ign_name False child
        child = M.singleton (node_name node) node

-- -----------------------------------------------------------
-- merge are used in construction to create a tree structure from [[]]
mergeTrees :: InstTree -> InstTree -> InstTree
mergeTrees t1 t2 = M.unionWith mergeNodes t1 t2

mergeTreeList :: [InstTree] -> InstTree
mergeTreeList = foldr mergeTrees M.empty

-- merge nodes in parallel InstTrees (used to turn single tree in shared tree)
mergeNodes :: InstNode -> InstNode -> InstNode
mergeNodes l1@(Loc {node_children = c1 })
            l2@(Loc {node_children = c2 }) | node_name l1 == node_name l2=
  let merged_child = mergeTrees c1 c2
      merged_type = case (node_type l1, node_type l2) of
                      (Just t1, Just t2) -> toMaybe (t1 == t2) t1
                      _ -> Nothing
  in l1 { node_children = merged_child,
          node_type = merged_type
        }

mergeNodes n1 n2 = internalError ("InstNodes: incompatible tree merge: " ++
                                  ppReadable (n1,n2))

-- -----------------------------------------------------------
-- Use use a State monad to memoize conversions from IType to CType as needed in the InstNode.
type M a = State (M.Map IType CType) a

iToCTM :: IType -> M CType
iToCTM itype = do
  cache <- get
  case (M.lookup itype cache) of
    Just t -> return t
    Nothing -> do
      let t' = iToCT itype
      put (M.insert itype t' cache)
      return t'

convISLPC :: IStateLocPathComponent -> M InstLoc
convISLPC islpc = do
  ct <- iToCTM (isl_ifc_type islpc)
  let  name = isl_inst_id islpc
       pos = getPosition name
       finalName = maybe name (mkId pos) (getIdDisplayName name)
       ignore = isl_inst_ignore islpc && (not $ isl_vector islpc)
  return (finalName,
          ct,
          isl_unique_index islpc,
          ignore,
          isl_inst_ignore_name islpc)

convIStateLoc :: IStateLoc -> M [InstLoc]
convIStateLoc = mapM convISLPC


-- -----------------------------------------------------------
-- Main entry point for InstTree construction
mkInstTree :: IModule a -> InstTree
mkInstTree imod = optTrace result
 where inst_tree = mkInstTree' imod
       transform_tree = compressIgnoredChildren
       result = transform_tree inst_tree
       tracethis = trace ("Inst tree \n" ++ ppReadable inst_tree ++ "\n") .
                   -- trace ("Ref tree\n"   ++ ppReadable ref_tree  ++ "\n") .
                   trace ("Final tree\n" ++ ppReadable result ++ "\n")
       optTrace = if doTraceTree then tracethis else id

mkInstTree' :: IModule a -> InstTree
mkInstTree' imod = optTrace (mergeTreeList singleTrees)
  where optTrace = if doTraceTree then tracethis else id
        tracethis = trace ("Tree: " ++ ppReadable (zip sv_nodes sv_locs))
                    . trace ("Unmerged: " ++ ppReadable singleTrees)
                    -- . trace ("RTree: " ++ ppReadable (zip sv_nodes (map mkRefLocs sv_locs))) $
        (sv_pairs, rule_pairs) = getIStateLocs imod
        (sv_ids, sv_isls) = unzip sv_pairs
        (rule_ids, rule_isls) = unzip rule_pairs
        -- The leaf nodes for the tree
        sv_nodes = map StateVar sv_ids
        rule_nodes = map Rule rule_ids
        -- [InstLoc] for each StateVar and Rule IModule
        (sv_locs, rule_locs) = (evalState $ do
              sv_conv <- mapM convIStateLoc sv_isls
              rule_conv <- mapM convIStateLoc rule_isls
              return (sv_conv, rule_conv)) M.empty
        svTrees = zipWith mkSingleTree sv_nodes sv_locs
        ruleTrees = zipWith mkSingleTree rule_nodes rule_locs
        singleTrees = svTrees ++ ruleTrees

-- -----------------------------------------------------------

getIStateLocs :: IModule a -> ([(Id, IStateLoc)], [(Id, IStateLoc)])
getIStateLocs imod = --trace ("StateVarLoc: " ++ ppReadable state_var_locs) $
                     (state_var_locs, rule_locs)
  where state_vars = imod_state_insts imod
        state_var_locs = mapSnd isv_isloc state_vars
        IRules _ rules = imod_rules imod
        rule_locs = zip (map getIRuleId rules) (map getIRuleStateLoc rules)

-- #############################################################################
-- #
-- # isHidden   -> return True if the Instnode:
-- #                 o is marked as hidden (isHideId is True)
-- #                 o is associated with a compiler-geretaed interface
-- #
-- # isHiddenKP -> return True if the Instnode:
-- #                 o is marked as hidden (isHideId is True)
-- #                 o is associated with a compiler-geretaed interface
-- #                 o has a single child that is a StateVar
-- #
-- #############################################################################

isHidden :: InstNode -> Bool
isHidden i = isHidden' False False i

isHiddenKP :: InstNode -> Bool
isHiddenKP i = isHidden' False True i

isHiddenAll :: InstNode -> Bool
isHiddenAll i = isHidden' True False i

isHidden' :: Bool -> Bool -> InstNode -> Bool
isHidden' True _ y@(Loc  {node_name = i }) | isHideAllId i = True
isHidden' True _ _ = False
isHidden' _ _    y | isUniquifier True y = False
isHidden' _ True y@(Loc  {node_name = i }) |isHideId i =
         case (M.elems $ node_children y) of
                  [StateVar {}] -> False
                  _             -> True
isHidden' _ False y@(Loc  {node_name = i })| isHideId i          = True
isHidden' _ _     Loc  {node_type = (Just t)} | isGeneratedIfc t = True
isHidden' _ _     Rule {node_name = i }       | isHideId i       = True
isHidden' _ _     _                                              = False

isGeneratedIfc :: CType -> Bool
isGeneratedIfc t = case leftCon t of
                     Nothing -> False
                     Just cid -> isGenId cid

-- isUniquifier :: Bool -> InstNode -> Bool
-- isUniquifier True y | isHiddenAll y        = False
-- isUniquifier hide y@(Loc {uniquified = u, node_name = n}) =
--           let xs = (nodeChildren hide y)
--               keep [y] | isNaked y    = False
--               keep []                 = False
--               keep _                  = True
--           in if (u && keep xs) then trace("NAME:" ++ show n ++ show xs) $ True else False
-- isUniquifier _ _                           = False

isUniquifier :: Bool -> InstNode -> Bool
isUniquifier True y | isHiddenAll y        = False
isUniquifier hide y@(Loc {uniquified = u, node_name = n}) =
          let xs = (nodeChildren hide y)
              keep (_:_:_)            = True -- at least 2 children
              keep [StateVar {}]      = True
              keep _                  = False
          in u && keep xs
isUniquifier _ _                           = False

nodeChildren :: Bool -> InstNode -> [InstNode]
nodeChildren hide i =
 let result = nodeChildren' hide i
 in case (result) of
    [x@(Loc {})] | (isHidden x && hide) -> (M.elems $ node_children x)
    _                                   -> result

nodeChildren' :: Bool -> InstNode -> [InstNode]
nodeChildren' False i@(Loc {}) = M.elems $ node_children i
nodeChildren' True i@(Loc {}) =
  let getList x | isHiddenAll x = []
      getList x@(Loc {}) | isHiddenKP x = concatMap getList (M.elems $ node_children x)
      getList x | isHiddenKP x = []
      getList x = [x]
  in concatMap getList (M.elems $ node_children i)

nodeChildren' _ _ = []


comparein ::   InstNode -> InstNode -> Ordering
comparein l r =
 let res = comparing (getPosition . node_name) l r
 in if (res == EQ) then cmpSuffixedIdByName (node_name l) (node_name r) else res

-- -----------------------------------------------------------
