// Test: Typeclass in constraint (Phase 1)
// Expected: NO warning - Helper is used via Describable constraint

package TypeclassConstraint;

import Helper::*;

// Function with typeclass constraint from Helper
function String describeIt(a x) provisos (Describable#(a));
    return describe(x);
endfunction

endpackage
