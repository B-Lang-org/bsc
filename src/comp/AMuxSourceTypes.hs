-- Recover source interpretations at scheduled method connections.
module AMuxSourceTypes (propagateArgumentMuxTypes) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import ASyntax
import ISyntax (IType(..))
import ISyntaxUtil (itBit)
import ATypePropagation (propagateSourceTypes, muxDataChildren)
import VModInfo (VFieldInfo(..), vFields)

-- Run immediately after AState, while connection IDs still use method names
-- and before inlining RWire/CReg instances. The VMI identifies data arguments
-- and results; names such as MUX/VAL are never used to guess a signal's role.
-- Match results against actual state outputs, since a method may use fewer
-- copies than its declared multiplicity.
propagateArgumentMuxTypes :: ASPackage -> ASPackage
propagateArgumentMuxTypes pkg = pkg { aspkg_expr_types = propagated }
  where
    defs = aspkg_values pkg ++ aspkg_inout_values pkg
    defmap = M.fromList [(i, t) | ADef i t _ _ <- defs]
    outputmap = M.fromList (aspkg_state_outputs pkg)
    argumentSeeds =
        [(ASDef t i, S.singleton sourceType) |
          inst <- aspkg_state_instances pkg,
          Method { vf_name = method, vf_mult = mult, vf_inputs = groups }
              <- vFields (avi_vmi inst),
          copy <- if mult > 1 then map Just [0 .. mult - 1] else [Nothing],
          (argN, ports) <- zip [1..] groups,
          (portM, (portName, _)) <- zip (splitPortNums ports) ports,
          Just sourceType <- [M.lookup portName (avi_port_types inst)],
          not (isBareBit sourceType),
          let i = mkMethId (avi_vname inst) method copy (MethodArg argN portM),
          Just t <- [M.lookup i defmap]]
    resultSeeds =
        [(ASPort t i, S.singleton sourceType) |
          inst <- aspkg_state_instances pkg,
          Method { vf_name = method, vf_mult = mult, vf_outputs = ports }
              <- vFields (avi_vmi inst),
          copy <- if mult > 1 then map Just [0 .. mult - 1] else [Nothing],
          (portM, (portName, _)) <- zip (splitPortNums ports) ports,
          Just sourceType <- [M.lookup portName (avi_port_types inst)],
          not (isBareBit sourceType),
          let i = mkMethId (avi_vname inst) method copy (MethodResult portM),
          Just t <- [M.lookup i outputmap]]
    propagated = propagateSourceTypes muxDataChildren defs
                      (aspkg_expr_types pkg ++ argumentSeeds ++ resultSeeds)
    isBareBit (ITAp t _) = t == itBit
    isBareBit _ = False
