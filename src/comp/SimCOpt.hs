module SimCOpt ( simCOpt ) where

import Flags
import SimCCBlock
import ASyntax
import ASyntaxUtil
import Id( Id, getIdBaseString, setIdBaseString
         , getIdQualString, setIdQualString
         , unQualId, isFire )
import ABinUtil(InstModMap)
import ErrorUtil(internalError)
import Util(mapSnd)
import SimPrimitiveModules(isPrimitiveModule)

import Data.Maybe(maybeToList)
import Data.List(find, intercalate)
import Data.List.Split(split, condense, oneOf)
import qualified Data.Map as M
import qualified Data.Set as S

import PPrint

-- import Debug.Trace

simCOpt :: Flags -> InstModMap ->
           ([SimCCBlock], [SimCCSched], [SimCCClockGroup], SimCCGateInfo) ->
           ([SimCCBlock], [SimCCSched], [SimCCClockGroup], SimCCGateInfo)
simCOpt flags instmodmap (blocks, scheds, clk_groups, gate_info) =
  let (blocks1,scheds1) = moveDefsOntoStack flags instmodmap (blocks,scheds)
      blocks2           = map (mapBlockFns removeUnusedLocals) blocks1
      scheds2           = map (mapSchedFns removeUnusedLocals) scheds1
  in (blocks2, scheds2, clk_groups, gate_info)


-- ---------------------
-- type used to keep track of writers and readers for each def

type FnLoc = (String,Bool)  -- fn name, is_schedule
data DefRecord = DF (S.Set FnLoc) (S.Set FnLoc)  -- writers, readers

printFnLoc :: FnLoc -> Doc
printFnLoc (s,_) = text s

instance PPrint DefRecord where
    pPrint _ _ (DF ws rs) =
        let wtxt = map printFnLoc (S.toList ws)
            rtxt = map printFnLoc (S.toList rs)
        in (text "Writers:") $+$ (nest 2 (commaSep wtxt)) $+$
           (text "Readers:") $+$ (nest 2 (commaSep rtxt))

-- create records for a bunch of reads or writes
readsIds :: FnLoc -> [AId] -> [(AId, DefRecord)]
fl `readsIds`  ids = [ (aid,DF S.empty (S.singleton fl)) | aid <- ids]
writesIds :: FnLoc -> [AId] -> [(AId, DefRecord)]
fl `writesIds` ids = [ (aid,DF (S.singleton fl) S.empty) | aid <- ids]

combine_refs :: DefRecord -> DefRecord -> DefRecord
combine_refs (DF w1 r1) (DF w2 r2) = DF (w1 `S.union` w2) (r1 `S.union` r2)

-- Get the AIds read or written by a SimCCFn
getFnRefs :: Bool -> SimCCFn -> [(AId, DefRecord)]
getFnRefs is_sched fn = concatMap (helper (sf_name fn, is_sched)) (sf_body fn)
  where helper fl (SFSDef _ (_,_)   Nothing)  = []
        helper fl (SFSDef _ (_,aid) (Just e)) = (fl `writesIds` [aid]) ++
                                                (fl `readsIds` (aVars e))
        helper fl (SFSAssign _ aid e)         = (fl `writesIds` [aid]) ++
                                                (fl `readsIds` (aVars e))
        helper fl (SFSAction act)             = fl `readsIds` (aVars act)
        helper fl (SFSAssignAction _ aid act _) = (fl `writesIds` [aid]) ++
                                                (fl `readsIds` (aVars act))
        helper fl (SFSRuleExec _)             = []
        helper fl (SFSCond e ts fs)           = (fl `readsIds` (aVars e)) ++
                                                (concatMap (helper fl) ts) ++
                                                (concatMap (helper fl) fs)
        helper fl (SFSMethodCall obj meth args) =
            concatMap (\e -> fl `readsIds` (aVars e)) args
        helper fl (SFSFunctionCall obj func args) =
            concatMap (\e -> fl `readsIds` (aVars e)) args
        helper fl (SFSResets stmts)           = concatMap (helper fl) stmts
        helper fl (SFSReturn Nothing)         = []
        helper fl (SFSReturn (Just e))        = fl `readsIds` (aVars e)
        helper fl (SFSOutputReset rstId e)    =
            -- the rstId doesn't exist as an entity in the SimCCBlock
            fl `readsIds` (aVars e)


-- ---------------------
-- Optimization that analyzes def usage and moves defs
-- to be stack-local in the schedule function or block SimCCFns.
-- This reduces the size of the class, improves cache effects and
-- optimizations and reduces memory traffic, VCD size, etc. by not
-- storing unneeded temporaries.  This will also remove entirely any
-- defs which are defined but not used anywhere.
moveDefsOntoStack :: Flags -> InstModMap -> ([SimCCBlock],[SimCCSched]) ->
                     ([SimCCBlock],[SimCCSched])
moveDefsOntoStack flags instmodmap (blocks,scheds) =
  let -- find all defs used in the blocks
      block_refs = [((sb_id b, aid), dr)
                   | b <- blocks
                   , let fns = (get_rule_fns b)++(get_method_fns b)++(sb_resets b)
                   , (aid,dr) <- concatMap (getFnRefs False) fns
                   ]
      block_defs = M.fromListWith combine_refs block_refs

      -- find all defs used in the schedule functions
      modsbmap = M.fromList [ (sb_name b, b) | b <- blocks ]
      -- Construct maps from (sbid, name) -> refs and
      --                     (sbid, name) -> qual_id used in schedule
      -- Because we will need both later.
      sched_tups = [ ((sbid, unqual_id), (dr, qual_id))
                   | s <- scheds
                   , let fns = (sched_fn s):(maybeToList (sched_after_fn s))
                   , (qual_id,dr) <- concatMap (getFnRefs True) fns
                   , let inst = getIdQualString (dropTopInst qual_id)
                   , let mod = M.findWithDefault (internalError $ "Unknown instance " ++ inst)
                                                 inst
                                                 instmodmap
                   , not (isPrimitiveModule mod)
                   , let mb = M.lookup mod modsbmap
                   , let blk = case mb of
                                 (Just b) -> b
                                 Nothing  -> internalError $ "No block for " ++ mod
                   , let unqual_id = unQualId qual_id
                   , let sbid = sb_id blk
                   ]
      sched_refs = [ (k, dr) | (k, (dr,_)) <- sched_tups ]
      sched_defs = M.fromListWith combine_refs sched_refs
      sched_qids = M.fromListWith S.union [ (k, S.singleton q) | (k,(_,q)) <- sched_tups ]

      all_defs = M.unionWith combine_refs block_defs sched_defs

      -- build a map from (BlockId,Id) to AType for all defs we
      -- might want to move
      btype_map = M.fromList [((sb_id b, aid),ty)
                             | b <- blocks
                             , let defs = (sb_publicDefs b) ++
                                          (sb_privateDefs b) ++
                                          [(t,i) | (t,i,_) <- sb_methodPorts b]
                             , (ty,aid) <- defs
                             ]

      -- record which Ids are for ports
      port_set = S.fromList [ (sb_id b, aid) | b <- blocks, (_,aid,_) <- sb_methodPorts b ]

      -- record which Ids are for ATaskAction
      atask_set = S.fromList [ (sb_id b, aid) | b <- blocks, aid <- sb_taskDefs b ]

      -- find the sb_id of the top-level module
      top_sbid = do mod <- M.lookup "" instmodmap
                    blk <- find (\b -> sb_name b == mod) blocks
                    return (sb_id blk)

      -- until performance issues with wide data are resolved, do not move
      -- wide values into the function, since they pay a construction penalty
      -- on each call.  also don't move string constructors.
      shouldMove (sbid,aid) =
          let sizeOkToMove = case (M.lookup (sbid,aid) btype_map) of
                                 (Just ty) -> (ty == ATReal) ||
                                              ((not (isStringType ty)) &&
                                               (not (isTupleType ty)) &&
                                               ((aSize ty) <= 64))
                                 Nothing   -> False
              -- don't move AV task defs
              exprOkToMove = S.notMember (sbid,aid) atask_set
              -- only move CF or WF if -keep-fires is not set
              cfwfOkToMove = not ((isFire aid) && (keepFires flags))
              -- only move ports if -keep-fires is not set
              isPort = (sbid,aid) `S.member` port_set
              portOkToMove = not (isPort && (keepFires flags))
              -- do not move ports if this is the top module of a SystemC model
              isTopSysC = (genSysC flags) && (top_sbid == (Just sbid))
              syscOkToMove = not (isPort && isTopSysC)
          in and [ sizeOkToMove
                 , exprOkToMove
                 , cfwfOkToMove
                 , portOkToMove
                 , syscOkToMove
                 ]

      -- determine which defs we want to move into each function
      move_map = M.fromListWith (++) [ (dest, [(sbid,aid)])
                                     | ((sbid, aid), DF ws rs) <- M.toList all_defs
                                     , let fs = ws `S.union` rs
                                     , (S.size fs) == 1
                                     , let (fn,is_schedule) = S.findMin fs
                                     , shouldMove (sbid,aid)
                                     , let dest = if is_schedule
                                                  then (Nothing,fn)
                                                  else (Just sbid,fn)
                                     ]
      moved_defs = M.fromListWith S.union [ (sbid, S.singleton aid)
                                          | els <- M.elems move_map
                                          , (sbid, aid) <- els
                                          ]

      -- determine which defs we want to delete entirely
      def_set = S.fromList [ (sb_id b, aid)
                           | b <- blocks
                           , aid <- map snd ((sb_publicDefs b) ++ (sb_privateDefs b))
                           ]
      unused_defs = def_set `S.difference` (M.keysSet all_defs)
      deleted_defs = M.fromListWith S.union
                                    [ (sbid, S.singleton aid)
                                    | (sbid, aid) <- S.toList unused_defs
                                    ]

      -- update blocks and functions
      isNotDeleted sbid aid =
          let moved = M.findWithDefault S.empty sbid moved_defs
              deleted = M.findWithDefault S.empty sbid deleted_defs
          in (aid `S.notMember` deleted) && (aid `S.notMember` moved)
      sndOf3 (_,x,_) = x
      inline aid = let q = getIdQualString aid
                       b = getIdBaseString aid
                       segs = filter (/=".") $ split (condense (oneOf ".")) q
                       name = intercalate "_" $ (map ("INST_"++) segs) ++ ["DEF_" ++ b]
                   in setIdBaseString (unQualId aid) name
      btype_lookup i = case M.lookup i btype_map of
                         Just ty -> ty
                         _ -> internalError "SimCOpt.moveDefsOntoStack btype_lookup"
      moveDefs (Just sbid) fn =  -- move within block
          let fname = sf_name fn
              new_defs = [ SFSDef isPort (ty,aid) Nothing
                         | (_,aid) <- M.findWithDefault [] ((Just sbid),fname) move_map
                         , let ty = btype_lookup (sbid,aid)
                         , let isPort = S.member (sbid,aid) port_set
                         ]
              body = new_defs ++ (sf_body fn)
          in fn { sf_body = body }
      moveDefs Nothing fn = -- move into schedule
          let fname = sf_name fn
              new_defs = [ [ SFSDef isPort (ty,qual_id) Nothing
                           | qual_id <- S.toList qids
                           ]
                         | (sbid,aid) <- M.findWithDefault [] (Nothing,fname) move_map
                         , let ty = btype_lookup (sbid,aid)
                         , let isPort = S.member (sbid,aid) port_set
                         , let qids = M.findWithDefault S.empty (sbid, aid) sched_qids
                         ]
              idmap = M.fromList [ (qual_id, inline qual_id)
                                 | (sbid,aid) <- M.findWithDefault [] (Nothing,fname) move_map
                                 , let qids = M.findWithDefault S.empty (sbid,aid) sched_qids
                                 , qual_id <- S.toList qids
                                 ]
              body = map (renameIds idmap) ((concat new_defs) ++ (sf_body fn))
          in fn { sf_body = body }
      blocks' = [ b { sb_publicDefs  = pubs
                    , sb_privateDefs = privs
                    , sb_methodPorts = ports
                    , sb_rules       = rls
                    , sb_methods     = meths
                    }
                | b <- blocks
                , let sbid  = sb_id b
                , let pubs  = filter ((isNotDeleted sbid) . snd) (sb_publicDefs b)
                , let privs = filter ((isNotDeleted sbid) . snd) (sb_privateDefs b)
                , let ports = filter ((isNotDeleted sbid) . sndOf3) (sb_methodPorts b)
                , let rls   = [ (mcd, mapSnd (moveDefs (Just sbid)) fns)
                              | (mcd, fns) <- sb_rules b
                              ]
                , let meths = [ (mcd, mapSnd (moveDefs (Just sbid)) fns)
                              | (mcd,fns) <- sb_methods b
                              ]
                ]
      scheds' = [ s { sched_fn = moveDefs Nothing (sched_fn s)
                    , sched_after_fn = fmap (moveDefs Nothing) (sched_after_fn s)
                    }
                | s <- scheds
                ]

  in (blocks',scheds')

dropTopInst :: Id -> Id
dropTopInst a = let q = (dropWhile (/= '.')) (getIdQualString a)
                in if (null q)
                   then unQualId a
                   else setIdQualString a (tail q)

-- ---------------------
-- Optimization that removes unused local defs from a SimCCFn
-- Note: this is a cheap and cheerful optimization that just handles
-- the simplest case.  It is not a proper dead/unreachable code
-- eliminator.  If we ever get around to doing proper analysis &
-- optimization then this pass can be removed.

removeUnusedLocals :: SimCCFn -> SimCCFn
removeUnusedLocals fn =
    let used_defs = S.fromList [ aid
                               | (aid, DF wr rd) <- getFnRefs False fn
                               , not (S.null rd)
                               ]
        action_values = S.fromList [ aid | (SFSAssignAction _ aid _ _) <- sf_body fn ]
        keep_defs = (used_defs `S.union` action_values)

        local_defs = S.fromList [ aid | (SFSDef _ (_,aid) _) <- sf_body fn ]

        args = S.fromList (map snd (sf_args fn))

        -- consider any unreferenced def to be unused, as well as any argument ports
        -- since the argument will be referenced directly
        isUnusedDef (SFSDef p (_,aid) _) =
            (aid `S.notMember` keep_defs) || (p && (aid `S.member` args))
        -- consider any assignment to a local unreferenced def to be unused, as well
        -- assignments to locally defined argument ports, since the argument will be
        -- referenced directly
        isUnusedDef (SFSAssign p aid _)  =
            (aid `S.member` local_defs) &&
            ((aid `S.notMember` keep_defs) || (p && (aid `S.member` args)))
        -- keep everything else
        isUnusedDef _                    = False

        body = [ stmt | stmt <- sf_body fn, not (isUnusedDef stmt) ]
    in fn { sf_body = body }

-- ---------------------
-- Utility routines for mapping over SimCCFns in blocks and schedules

mapFnSet :: (SimCCFn -> SimCCFn) -> SBFnSet -> SBFnSet
mapFnSet f (mcd,fs) = (mcd, mapSnd f fs)

mapBlockFns :: (SimCCFn -> SimCCFn) -> SimCCBlock -> SimCCBlock
mapBlockFns f blk =
    let rules = map (mapFnSet f) (sb_rules blk)
        meths = map (mapFnSet f) (sb_methods blk)
        rsts  = map f (sb_resets blk)
    in blk { sb_rules   = rules
           , sb_methods = meths
           , sb_resets  = rsts
           }

mapSchedFns :: (SimCCFn -> SimCCFn) -> SimCCSched -> SimCCSched
mapSchedFns f sch =
    let sf  = f (sched_fn sch)
        saf = fmap f (sched_after_fn sch)
    in sch { sched_fn       = sf
           , sched_after_fn = saf
           }
