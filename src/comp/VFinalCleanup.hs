module VFinalCleanup (finalCleanup) where

import Data.List(nub)
import qualified Data.Map as M
import qualified Data.Set as S
import Position(noPosition)
import Flags(Flags, keepFires, removeUnusedMods, finalcleanup, keepInlined)
import Id
import FStringCompat(mkFString)
import ASyntax
import ASyntaxUtil
import BackendNamingConventions(createVerilogNameMapForAVInst)

--import Debug.Trace
-- import Util(traces)


-- ==============================

-- Build a state  containing:
--   * the names of the visited instances (for quick lookup)
--   * a map from local signal names to their definitions
--   * the instances in the module
--   * the instances that have been reached (and are thus connected)

-- Note: We make the assumption that all ports of a state element or
-- sub module are connected.  If we enter a submodule port, we add
-- all the submodule's ports to the connected list.

data ConnState = ConnState {
                     visited_wires :: S.Set AId,  -- marking for visited nodes
                     visited_insts :: S.Set AId,
                     defs          :: M.Map AId ADef,
                     instances     :: M.Map AId AVInst,  -- instances from the package
                     flags         :: Flags
                 }

-- ==============================

-- Final cleanup of the ASyntax before Verilog generation.
--  * removes unused state module if flag is set
--  * removes unused variables introduced during veri quirks
finalCleanup :: Flags -> ASPackage -> ASPackage
finalCleanup flags pin = (unusedm) pin
    where
      unusedm = if (cleanup) then removeUnusedInsts flags else id
      -- only do this phase if the LSB of the flag is 1
      -- (this flag may be extended to have other functions for other bits)
      cleanup = odd $ finalcleanup flags


-- Returns the package with only the wires and instances which are
-- connected to an output.  (Optionally keeps all the instances, and
-- their port connection, if the removeUnusedMods flag is off.)
--   Note: This assumes that all foreign function calls are connected.
--   Typically synthesizable modules will not have any foreign functions.
--   Note: Removed instances also need to have their ports removed from
--   the state output list in the ASPackage.  XXX hack used to do this
removeUnusedInsts :: Flags -> ASPackage -> ASPackage
removeUnusedInsts flags package =
    package { aspkg_state_instances = ss'',
              aspkg_state_outputs = sos',
              aspkg_values = ds' }
    where
          keepInlinedMods = keepInlined flags
          ds = aspkg_values package
          ss = aspkg_state_instances package
          sos = aspkg_state_outputs package

          os = aspkg_outputs package
          ios = aspkg_inouts package
          fs = aspkg_foreign_calls package

          (cdefs,cinsts) = -- traces("conn outputs is: " ++ ppReadable markedConn) $
                           -- traces("conn package: " ++ ppReadable package ) $
                           connectedNode flags markedConn ss ds
          ds' = filter isDefUsed ds
          isDefUsed :: ADef -> Bool
          isDefUsed def@(ADef i _ _ _) = S.member (adef_objid def) cdefs
          ss'' = if (removeUnusedMods flags)
                 then filter isModuleUsed ss
                 else ss
          isModuleUsed :: AVInst -> Bool
          isModuleUsed inst = S.member (avi_vname inst) cinsts
          sos' = if (removeUnusedMods flags)
                 then filter isPortOfConnectedInst sos
                 else sos
          isPortOfConnectedInst (i,_) =
              -- XXX This uses a hack (getRootName) to get the instance name
              (getRootName i) `S.member` (S.map (getIdString) cinsts)

          -- started with the outputs, any kept firing signals, any kept
          -- instances, and the wires used in foreign function calls
          avdefs = concat [afc_writes fc | (_,fcs) <- fs, fc <- fcs]
          markedConn :: [AId]
          markedConn = (map fst os) ++ (map fst ios) ++
                       fires ++ instconn ++
                       aVars fs ++ avdefs ++
                       inlinedports ++ keepEvenUnused
          instconn   = if (removeUnusedMods flags)
                       then []
                       else concatMap (getPortIdsFromInst flags) ss
          fires = if (keepFires flags)
                  then [i | def@(ADef i t e _) <- ds, isFire i ]
                  else []
          inlinedports = if (keepInlinedMods)
                         then aspkg_inlined_ports package
                         else []
          keepEvenUnused = [i | def@(ADef i _ _ _) <- ds, hasIdProp i IdP_keepEvenUnused]

-- return a  set of connected nodes and connected instances
connectedNode :: Flags -> [AId] -> [AVInst] ->  [ADef]  -> (S.Set AId, S.Set AId)
connectedNode flags outputs ainsts din = (visited_wires cstate, visited_insts cstate)
    where
    defMap  = M.fromList (map (\d@(ADef i _ _ _) -> (i,d))  din)
    instMap = M.fromList (map (\inst -> (avi_vname inst,inst)) ainsts)
    initState = (ConnState S.empty S.empty defMap instMap flags)
    cstate = connected initState outputs

-- traverse the design.
connected :: ConnState -> [AId] -> ConnState
connected cstate [] = cstate
connected cstate (h:rest) |  S.member h (visited_wires cstate) = connected cstate rest
connected cstate (h:rest) = connected cstate'  (newvars ++ rest )
    where
        (cstate', newvars) = case (M.lookup h (defs cstate)) of
                               Nothing    -> handleInst cstate h
                               Just def   -> handleExpr cstate h (adef_expr def)

-- pull out var from def
handleExpr :: ConnState -> Id -> AExpr -> (ConnState,[Id])
handleExpr cstate thisId thisExpr = (cstate',newvars)
    where
      cstate' = cstate { visited_wires = S.insert thisId (visited_wires cstate)}
      newvars = aVars thisExpr

handleInst :: ConnState -> Id -> (ConnState,[Id])
handleInst cstate instId = handleInst2 rootId
    where
      rootName = getRootName instId
      rootId   = mkId noPosition (mkFString rootName)
      --
      handleInst2 :: Id -> (ConnState,[Id])
      handleInst2 rid | rid `S.member` (visited_insts cstate) = (cstate,[])
      handleInst2 rid = (cstate',newvars)
          where
            cstate' = cstate { visited_insts = S.insert rid (visited_insts cstate),
                               visited_wires = S.insert instId (visited_wires cstate)}
            newvars = case (M.lookup rid (instances cstate)) of
                         Just i  -> getPortIdsFromInst (flags cstate) i
                         Nothing -> [] -- inputs have no defs

-- Get AIds from an instance, ports plus clock and reset
getPortIdsFromInst :: Flags -> AVInst -> [AId]
getPortIdsFromInst flags inst =
        cr ++ portids
    where
        cr = aVars inst
        (_,ports) = unzip $ createVerilogNameMapForAVInst flags inst
        portids = map (\s -> mkId noPosition s) (nub (ports))

-- XXX This is hack to get the instance name; need a better data model
getRootName :: Id -> String
getRootName id = takeWhile ((/=) '$') (getIdString id)
