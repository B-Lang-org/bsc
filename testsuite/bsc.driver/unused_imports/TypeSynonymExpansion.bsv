// Test: Type synonym expansion (Phase 1)
// Expected: NO warning - Helper is used via type synonym Byte

package TypeSynonymExpansion;

import Helper::*;

// Use Helper's Byte type synonym in a signature
function Byte getValue();
    return 42;
endfunction

endpackage
