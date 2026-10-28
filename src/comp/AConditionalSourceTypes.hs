-- Share candidate interpretations across conditional data alternatives.
-- This pass only augments metadata: it does not rewrite hardware expressions.
module AConditionalSourceTypes (propagateConditionalTypes, conditionalDataChildren) where

import ASyntax
import ASyntaxUtil (findAExprs)
import ATypePropagation (propagateSourceTypesFrom, muxDataChildren)
import Prim (PrimOp(..))

propagateConditionalTypes :: ASPackage -> ASPackage
propagateConditionalTypes pkg = pkg {
    aspkg_expr_types = propagateSourceTypesFrom dataChildren liveRoots
        (aspkg_values pkg ++ aspkg_inout_values pkg)
        (aspkg_expr_types pkg)
    }
  where
    -- Constructor arguments and foreign calls can contain selections which
    -- never acquire a named definition. Metadata roots are included by the
    -- engine itself, separately from these live hardware expressions.
    liveRoots = findAExprs (:[]) (aspkg_state_instances pkg) ++
                findAExprs (:[]) (aspkg_foreign_calls pkg)
    -- One closure covers alternating conditional and mux nests. The core
    -- additionally shares candidates through aliases and array selections.
    dataChildren e = muxDataChildren e ++ conditionalDataChildren e

conditionalDataChildren :: AExpr -> [Int]
conditionalDataChildren (APrim _ _ PrimIf [_, _, _]) = [1, 2]
conditionalDataChildren (APrim _ _ PrimCase (_ : _ : arms))
    | even (length arms) = 1 : [3,5 .. length arms + 1]
conditionalDataChildren _ = []
