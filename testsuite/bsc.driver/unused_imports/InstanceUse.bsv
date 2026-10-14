// Test: Typeclass instance usage (Phase 2)
// Expected: NO warning - Helper is used via instance resolution

package InstanceUse;

import Helper::*;

function String test();
    Byte b = 42;
    return describe(b);  // Uses Describable instance from Helper
endfunction

endpackage
