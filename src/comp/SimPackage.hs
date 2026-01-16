{-# LANGUAGE CPP #-}
module SimPackage(
                  -- types
                  SimSystem(..),
                  PackageMap,
                  InstModMap,

                  SimPackage(..),
                  DefMap,
                  AVInstMap,
                  MethodOrderMap,

                  SimSchedule(..),
                  SchedNode(..), getSchedNodeId,
                  DisjointRulesDB,

                  -- utilities
                  findPkg,
                  findSubPkg,
                  findDef,
                  findAVInst,
                  findMethodOrderSet,
                  findInstMod,

                  getSimPackageInputs,
                  getPortInfo,

                  exclRulesDBToDisjRulesDB
                 ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Eval
import ErrorUtil(internalError)
import PPrint
import Id
import IdPrint
import VModInfo
import Wires
import Pragma
import ASyntax
import ASyntaxUtil
import AScheduleInfo
import ABinUtil(InstModMap,ABinMap)
import SimDomainInfo
import ForeignFunctions(ForeignFuncMap)

import Control.Monad(when)
import Data.List(groupBy)
import qualified Data.Map as M
import qualified Data.Set as S

-- import Debug.Trace

-- This is a map from AId to the ADef which defines the value for that AId
type DefMap = M.Map AId ADef

-- This is a map from AId of an instantiated submodule to its information
type AVInstMap = M.Map AId AVInst

-- map from submodule instance name to a set of pairs of method names
-- where the first method must execute before the second
-- (when executed sequentially for atomic execution in one action)
type MethodOrderMap = M.Map AId (S.Set (AId, AId))

-- map from package Ids to SimPackages
type PackageMap = M.Map Id SimPackage

data SimSystem =
  SimSystem { ssys_packages    :: PackageMap
            , ssys_schedules   :: [SimSchedule]
            , ssys_top         :: Id  -- name of top package
            , ssys_instmap     :: InstModMap
            , ssys_ffuncmap    :: ForeignFuncMap
            , ssys_filemap     :: ABinMap
            , ssys_default_clk :: Maybe String
            , ssys_default_rst :: Maybe String
            }
  deriving (Show)

data SimPackage =
  SimPackage { sp_name :: Id
             , sp_is_wrapped :: Bool -- carryover
             , sp_version :: String -- from ABin
             , sp_pps :: [PProp] -- from ABinModInfo
             , sp_size_params :: [AId] -- carryover
             , sp_inputs :: [AAbstractInput] -- carryover
             , sp_clock_domains :: [AClockDomain] -- carryover?
             , sp_external_wires :: VWireInfo -- carryover?
             , sp_reset_list :: [(ResetId, AReset)] -- carryover?
             , sp_state_instances :: AVInstMap
             -- inst and mod name of noinline functions as modules
             , sp_noinline_instances :: [(String,String)]
             , sp_method_order_map :: MethodOrderMap
             , sp_local_defs :: DefMap
             , sp_rules :: [ARule]
             , sp_interface :: [AIFace]
             , sp_schedule :: AScheduleInfo
             , sp_pathinfo :: VPathInfo
             -- Assign numbers to the gates in a module, for codegen
             , sp_gate_map :: [AExpr]  -- order is [0..]
             -- if these are handled earlier, then not needed here:
             , sp_schedule_pragmas :: [ASchedulePragma] -- carryover?
             -- could include user-comments (generated in RTL)
             }
  deriving (Show)

-- Trimmed version of ExclusiveRulesDB, to hold just the disjoint info
type DisjointRulesDB = M.Map ARuleId (S.Set ARuleId)

data SimSchedule = SimSchedule
    { ss_clock :: AClock
    , ss_posedge :: Bool
    , ss_schedule :: ASchedule
    , ss_disjoint_rules_db :: DisjointRulesDB
    , ss_sched_graph :: [(SchedNode, [SchedNode])]
    , ss_sched_order :: [SchedNode]
    , ss_domain_info_map :: DomainInfoMap
    , ss_early_rules :: [ARuleId]
    }
  deriving (Show)

-- -----

instance PPrint SimSystem where
    pPrint d _ ssys =
        (text "SimSystem") $+$
        text "-- Packages" $+$
        pPrint d 0 (ssys_packages ssys) $+$
        text "-- Schedules" $+$
        pPrint d 0 (ssys_schedules ssys) $+$
        text "-- Top module" $+$
        ppId d (ssys_top ssys)

instance PPrint SimPackage where
    pPrint d _ spkg =
        (text "SimPackage" <+> ppId d (sp_name spkg) <>
         if (sp_is_wrapped spkg) then text " -- function" else empty) $+$
        text (sp_version spkg) $+$
        text "-- SimPackage parameters" $+$
        pPrint d 0 (sp_size_params spkg) $+$
        text "-- SimPackage arguments" $+$
        foldr ($+$) (text "") (map (pPrint d 0) (sp_inputs spkg)) $+$
        text "-- SimPackage wire info" $+$
        pPrint d 0 (sp_external_wires spkg) $+$
        text "-- SimPackage clock domains" $+$
        pPrint d 0 (sp_clock_domains spkg) $+$
        text "-- SimPackage resets" $+$
        pPrint d 0 (sp_reset_list spkg) $+$
        text "-- SP state elements" $+$
        foldr ($+$) (text "")
            (map (pPrint d 0) (M.elems (sp_state_instances spkg))) $+$
        text "-- SP noinline elements" $+$
        foldr ($+$) (text "")
            (map (pPrint d 0) (sp_noinline_instances spkg)) $+$
        text "-- SP method order map" $+$
        ppMethodOrderMap d (sp_method_order_map spkg) $+$
        text "-- SP local definitions" $+$
        foldr ($+$) (text "")
            (map (pPrint d 0) (M.elems (sp_local_defs spkg))) $+$
        text "-- SP rules" $+$
        foldr ($+$) (text "") (map (pPrint d 0) (sp_rules spkg)) $+$
        text "-- SP scheduling pragmas" $+$
        pPrint d 0 (sp_schedule_pragmas spkg) $+$
        text "-- SP interface" $+$
        foldr ($+$) empty
            [(text "-- SP  sp_interface def" <+> pPrint d 0 (sp_name spkg)) $+$
             pPrint d 0 i | i <- sp_interface spkg] $+$
        text "-- SP schedule" $+$
        pPrint d 0 (asi_schedule (sp_schedule spkg)) $+$
        text "-- SP path info" $+$
        pPrint d 0 (sp_pathinfo spkg) $+$
        text "-- SP gate map" $+$
        pPrint d 0 (sp_gate_map spkg)

ppMethodOrderMap :: PDetail -> MethodOrderMap -> Doc
ppMethodOrderMap d mmap =
    let ppOneInst (i, mset) = ppId d i $+$
                              nest 4 (foldr ($+$) (text "")
                                          (map (pPrint d 0) (S.toList mset)))
    in  foldr ($+$) (text "")
            (map ppOneInst (M.toList mmap))


instance PPrint SimSchedule where
    pPrint d _ simschedule =
        let label = text "SimSchedule"
            edge = text (if (ss_posedge simschedule)
                         then "posedge"
                         else "negedge")
            domain = text (show (ss_clock simschedule))
        in label $+$
           (nest 2 ((text "-- clock")    $+$
                    edge <+> domain      $+$
                    (text "-- schedule") $+$
                    pPrint d 0 (ss_schedule simschedule) $+$
                    (text "-- seq graph") $+$
                    pPrint d 0 (ss_sched_graph simschedule) $+$
                    (text "-- seq order") $+$
                    pPrint d 0 (ss_sched_order simschedule) $+$
                    (text "-- domain info map") $+$
                    pPrint d 0 (ss_domain_info_map simschedule) $+$
                    (text "-- early rules") $+$
                    pPrint d 0 (ss_early_rules simschedule)
                    ))

-- -----

instance NFData SimSystem where
    rnf ssim = rnf3 (ssys_packages ssim)
                    (ssys_schedules ssim)
                    (ssys_top ssim)

instance Eq SimPackage where
    sp1 == sp2 =
        (
         -- for the scheduleinfo, just check the schedule
         (asi_schedule (sp_schedule sp1) ==
             asi_schedule (sp_schedule sp2)) &&
         -- for the rest, use equality
         (sp_name sp1 == sp_name sp2) &&
         (sp_is_wrapped sp1 == sp_is_wrapped sp2) &&
         (sp_version sp1 == sp_version sp2) &&
         (sp_size_params sp1 == sp_size_params sp2) &&
         (sp_inputs sp1 == sp_inputs sp2) &&
         (sp_clock_domains sp1 == sp_clock_domains sp2) &&
         (sp_external_wires sp1 == sp_external_wires sp2) &&
         (sp_reset_list sp1 == sp_reset_list sp2) &&
         (sp_state_instances sp1 == sp_state_instances sp2) &&
         (sp_noinline_instances sp1 == sp_noinline_instances sp2) &&
         (sp_method_order_map sp1 == sp_method_order_map sp2) &&
         (sp_local_defs sp1 == sp_local_defs sp2) &&
         (sp_rules sp1 == sp_rules sp2) &&
         (sp_interface sp1 == sp_interface sp2) &&
         (sp_pathinfo sp1 == sp_pathinfo sp2) &&
         (sp_gate_map sp1 == sp_gate_map sp2) &&
         (sp_schedule_pragmas sp1 == sp_schedule_pragmas sp2)
        )

instance NFData SimPackage where
    rnf (SimPackage n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19) =
        rnf19 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19

instance NFData SimSchedule where
    rnf ssched =
        --- we only care about certain fields
        (
            (ss_clock ssched    == ss_clock ssched)
         && (ss_posedge ssched  == ss_posedge ssched)
         && (ss_schedule ssched == ss_schedule ssched)
         && (ss_sched_graph ssched == ss_sched_graph ssched)
         && (ss_sched_order ssched == ss_sched_order ssched)
         && (ss_domain_info_map ssched == ss_domain_info_map ssched)
         && (ss_early_rules ssched == ss_early_rules ssched)
        ) `seq` ()

-- -----

instance (Ord a, AExprs b) => AExprs (M.Map a b) where
    mapAExprs f m = let (ks,vs) = unzip (M.toList m)
                        vs'     = mapAExprs f vs
                    in M.fromList (zip ks vs')
    -- monadic
    mapMAExprs f m =
        do let (ks,vs) = unzip (M.toList m)
           vs' <- mapMAExprs f vs
           return $ M.fromList (zip ks vs')
    -- find
    findAExprs f m = findAExprs f (M.elems m)

instance AExprs SimPackage where
    mapAExprs f pack = pack {
        sp_interface = mapAExprs f (sp_interface pack),
        sp_rules = mapAExprs f (sp_rules pack),
        sp_state_instances = mapAExprs f (sp_state_instances pack),
        sp_local_defs = mapAExprs f (sp_local_defs pack) }
    -- monadic
    mapMAExprs f pack@(SimPackage { sp_interface = ifc,
                                    sp_rules = rs,
                                    sp_state_instances = insts,
                                    sp_local_defs = defs })
        = do ifc' <- mapMAExprs f ifc
             rs' <- mapMAExprs f rs
             insts' <- mapMAExprs f insts
             defs' <- mapMAExprs f defs
             return (pack { sp_interface = ifc',
                            sp_rules = rs',
                            sp_state_instances = insts',
                            sp_local_defs = defs' })
    -- find
    findAExprs f pack =
        findAExprs f (sp_interface pack) ++
        findAExprs f (sp_rules pack) ++
        findAExprs f (sp_state_instances pack) ++
        findAExprs f (sp_local_defs pack)

-- -----

-- Utilities

findPkg :: PackageMap -> Id -> SimPackage
findPkg pkg_map id =
    case M.lookup id pkg_map of
      Just pkg -> pkg
      Nothing  -> internalError ("SimPackage.findPkg: cannot find " ++
                                   ppReadable id)

findSubPkg :: SimSystem -> SimPackage -> AId -> Maybe SimPackage
findSubPkg ss parent path =
  let segments = filter (/=".") $ groupBy (\x y -> x /= '.' && y /= '.') (getIdString path)
  in findIt parent (map mk_homeless_id segments)
  where findIt p []     = Just p
        findIt p (x:xs) = let avi      = findAVInst (sp_state_instances p) x
                              mod_name = vName_to_id (vName (avi_vmi avi))
                              sub      = M.lookup mod_name (ssys_packages ss)
                          in case sub of
                               (Just s) -> findIt s xs
                               Nothing  -> Nothing

findDef :: DefMap -> AId -> ADef
findDef def_map id =
    case M.lookup id def_map of
        Just def -> def
        Nothing  -> internalError ("SimPackage.findDef: cannot find " ++
                                   ppReadable id)

findAVInst :: AVInstMap -> AId -> AVInst
findAVInst avinst_map id =
    case M.lookup id avinst_map of
        Just avi -> avi
        Nothing -> internalError ("SimPackage.findAVInst: cannot find " ++
                                  ppReadable id)

findMethodOrderSet :: MethodOrderMap -> AId -> S.Set (AId, AId)
findMethodOrderSet mmap id =
    case M.lookup id mmap of
        Just mset -> mset
        Nothing -> internalError ("SimPackage.findMethodOrderSet: " ++
                                  "cannot find " ++ ppReadable id)

findInstMod :: InstModMap -> String -> String
findInstMod inst_map inst =
    case M.lookup inst inst_map of
        Just mod -> mod
        Nothing -> internalError ("SimPackage.findInstMod: cannot find " ++
                                  ppReadable inst)

-- -----

-- XXX This wouldn't be needed if we called "getAPackageInputs" on
-- XXX the APackage and stored the result in SimPackage
getSimPackageInputs :: SimPackage -> [(AAbstractInput, VArgInfo)]
getSimPackageInputs spkg =
    let
        -- get the two fields
        inputs = sp_inputs spkg
        arginfos = wArgs (sp_external_wires spkg)

        -- check that they are the same length
        inputs_length = length (sp_inputs spkg)
        arginfos_length = length arginfos

        args_with_info = zip inputs arginfos
    in
        if (inputs_length /= arginfos_length)
        then internalError ("getSimPackageInputs: " ++
                            "length inputs != length arginfos: " ++
                            ppReadable (inputs, arginfos))
        else args_with_info

-- -----

getPortInfo :: [PProp] -> AIFace
            -> Maybe (AId, (Maybe VName, [(AType,AId,VName)], [(AType,VName)], Bool, [AId]))
getPortInfo pps aif =
    let name = aif_name aif
        vfi  = aif_fieldinfo aif
        en   = do e <- vf_enable vfi
                  -- always enabled implies enabled when ready
                  when (isEnWhenRdy pps name) (fail "no enable port")
                  return (fst e)
        args = aIfaceArgs aif
        ps   = map fst (vf_inputs vfi)
        ins  = [ (t,i,vn) | ((i,t),vn) <- zip args ps ]
        rts  = aIfaceResTypes aif
        rets  = zip rts $ map fst $ vf_outputs vfi
        isAction = case aif of
                     (AIAction {})      -> True
                     (AIActionValue {}) -> True
                     otherwise          -> False
        rules = map aRuleName (aIfaceRules aif)
    in case vfi of
         (Method {}) -> Just (name, (en, ins, rets, isAction, rules))
         otherwise   -> Nothing

-- -----

exclRulesDBToDisjRulesDB :: ExclusiveRulesDB -> DisjointRulesDB
exclRulesDBToDisjRulesDB (ExclusiveRulesDB emap) =
    let e_edges = M.toList emap
        convEdge (r,(ds,es)) = (r, ds)
        d_edges = map convEdge e_edges
    in  M.fromList d_edges

-- -----
