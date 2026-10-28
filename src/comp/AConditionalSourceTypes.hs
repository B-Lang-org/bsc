-- Propagate representation evidence through conditional data alternatives.
-- This pass only augments metadata: it does not rewrite hardware expressions.
module AConditionalSourceTypes (propagateConditionalTypes) where

import ASyntax
import ATypePropagation (propagateSourceTypes, muxDataChildren)
import Prim (PrimOp(..))

propagateConditionalTypes :: ASPackage -> ASPackage
propagateConditionalTypes pkg = pkg {
    aspkg_expr_types = propagateSourceTypes dataChildren
        (aspkg_values pkg ++ aspkg_inout_values pkg)
        (aspkg_expr_types pkg)
    }
  where
    -- Include the earlier argument-mux rule in this closure. A conditional
    -- branch can itself be a mux, and a mux arm can be another conditional;
    -- running the two rules once in sequence would miss alternating nests.
    dataChildren e = muxDataChildren e ++ conditionalDataChildren e

conditionalDataChildren :: AExpr -> [AExpr]
conditionalDataChildren (APrim _ _ PrimIf [_, yes, no]) = [yes, no]
conditionalDataChildren (APrim _ _ PrimCase (_ : def : arms)) =
    case caseValues arms of
        Just values -> def : values
        Nothing -> []
conditionalDataChildren _ = []

-- The case representation alternates label and value after selector/default.
-- An incomplete pair is not a data edge; leave malformed forms untouched.
caseValues :: [AExpr] -> Maybe [AExpr]
caseValues [] = Just []
caseValues (_ : value : rest) = fmap (value :) (caseValues rest)
caseValues _ = Nothing
