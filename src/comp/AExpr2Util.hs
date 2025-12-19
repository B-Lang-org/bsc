-- Common code used by various converters

module AExpr2Util(
  getMethodOutputPorts
) where

import qualified Data.Map as M
import Data.List(find)

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

-- -------------------------

