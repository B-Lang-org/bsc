-- Add numeric and Boolean interpretations justified by hardware operations.
module APrimitiveSourceTypes (propagatePrimitiveTypes) where

import ASyntax
import ASyntaxUtil (findAExprs)
import AConditionalSourceTypes (conditionalDataChildren)
import ATypePropagation (propagateSourceTypesWithPrimitives, muxDataChildren)

-- Run before synthesis/Verilog lowering removes signed operations. This
-- augments candidates only; it does not change hardware or replace observed
-- source types. Numeric primitives supply interpretations, not proof of the
-- user's original declaration.
propagatePrimitiveTypes :: ASPackage -> ASPackage
propagatePrimitiveTypes pkg = pkg {
    aspkg_expr_types = propagateSourceTypesWithPrimitives dataChildren roots
        (aspkg_values pkg ++ aspkg_inout_values pkg) (aspkg_expr_types pkg)
    }
  where
    roots = findAExprs (:[]) (aspkg_state_instances pkg) ++
            findAExprs (:[]) (aspkg_foreign_calls pkg)
    dataChildren e = muxDataChildren e ++ conditionalDataChildren e
