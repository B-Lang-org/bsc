-- Common code used by various converters

module AExpr2Util(
  getMethodOutputPorts,
  getSingleMethodOutputPort,
  getMethodOutputPortAt
) where

import qualified Data.Map as M
import Data.List(find, genericIndex)

import ErrorUtil(internalError)
import PPrint
import Id(qualEq)
import ASyntax
import VModInfo(VModInfo(..), VFieldInfo(..), vName_to_id)


-- -------------------------

-- Different methods on submodules might be defined to use the same ports,
-- so two AMethCall expressions might differ but be logically equivalent.
-- If we declare separate variables for the two calls, then the solver will
-- not recognize that they are equal.  Rather than assert all of the
-- equivalences in the solver's context, we can reduce each AMethCall to a
-- canonical form before declaring a variable.  The canonical form is defined
-- to be the same for two AMethCalls that are logically equivalent.

-- This canonicalization needs to happen for any expression with arguments
-- that is being replaced with a variable, because method calls might appear
-- in the arguments.

-- XXX For SMT solvers, instead of replacing foreign expressions with a variable,
-- XXX we can replace them with an unevaluated function applied to its arguments!
-- XXX That way, the SMT solver will handle any equivalence of the arguments.

getMethodOutputPorts :: (M.Map AId VModInfo) -> AId -> AId -> [AId]
getMethodOutputPorts stateMap modId methId =
  let mod_err = internalError("canonMethCalls: module not found: " ++
                              ppReadable modId)
      fields = vFields $ M.findWithDefault mod_err modId stateMap
      meth_err = internalError("canonMethCalls: method not found: " ++
                               ppReadable (modId, methId))
      findFn (Method { vf_name = i }) = qualEq i methId
      findFn _ = False
      ports = case (find findFn fields) of
                Just (Method { vf_outputs = os }) -> os
                _ -> meth_err
      out_err = internalError("canonMethCalls: method has no output: " ++
                              ppReadable (modId, methId))
  in  if null ports then out_err else map (vName_to_id . fst) ports

-- A bare method reference (with no tuple selection) refers to a method with a
-- single output port.  Return that (canonical) port, failing if the method has
-- multiple output ports (those must be reached through a tuple selector).
getSingleMethodOutputPort :: (M.Map AId VModInfo) -> AId -> AId -> AId
getSingleMethodOutputPort stateMap modId methId =
  case getMethodOutputPorts stateMap modId methId of
    [portId] -> portId
    ports -> internalError ("getSingleMethodOutputPort: unexpected output ports: " ++
                            ppReadable (modId, methId, ports))

-- The output port at the given tuple-selector index, for a method whose result
-- is split across multiple output ports.  ATupleSel indices are 1-based (AConv
-- builds them as idx + 1), while getMethodOutputPorts is a 0-based list, so
-- shift by one to index it.
getMethodOutputPortAt :: (M.Map AId VModInfo) -> AId -> AId -> Integer -> AId
getMethodOutputPortAt stateMap modId methId selIdx =
  getMethodOutputPorts stateMap modId methId `genericIndex` (selIdx - 1)

-- -------------------------

