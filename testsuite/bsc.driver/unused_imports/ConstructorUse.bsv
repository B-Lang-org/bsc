// Test: Constructor usage (Phase 2)
// Expected: NO warning - Helper is used via constructor

package ConstructorUse;

import Helper::*;

function Color getColor();
    return Red;  // Uses Red constructor from Helper
endfunction

endpackage
