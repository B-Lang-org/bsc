// Test: Transitive synonym expansion (Phase 1)
// Expected: NO warning for HelperAlias or Helper - both used via MyByte synonym chain

package TransitiveSynonymOK;

import HelperAlias::*;  // MyByte = Byte (from Helper)

// Using MyByte which expands to Byte which expands to Bit#(8)
function MyByte getValue();
    return 42;
endfunction

endpackage
