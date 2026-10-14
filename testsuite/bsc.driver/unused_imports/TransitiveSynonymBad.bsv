// Test: Transitive synonym expansion (Phase 1)
// Expected: NO warning for HelperAlias or Helper - both used via MyByte synonym chain

package TransitiveSynonymBad;

import HelperAlias::*;  // MyByte = Byte (from Helper)
import Helper::*;       // Byte is not used directly so this is unnecessary,
                        // but we do not get the warning because Byte does
			// come up during synonym expansion.

// Using MyByte which expands to Byte which expands to Bit#(8)
function MyByte getValue();
    return 42;
endfunction

endpackage
