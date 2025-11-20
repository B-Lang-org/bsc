// Test: Using orphan instance (Phase 2)
// Expected: NO warning - OrphanInstance is used via instance resolution
//           Helper may warn if not used otherwise

package OrphanInstanceUse;

import OrphanInstance::*;  // Has orphan Describable#(Bool) instance

function String test();
    Bool b = True;
    return describe(b);  // Uses orphan instance from OrphanInstance
endfunction

endpackage
