// Test: Local export using imported type (Phase 2)
// Expected: NO warning - Helper's Byte type is used in exported function signature

package LocalExportWithImportedType;

import Helper::*;

// Local function using imported type
function Byte double(Byte x);
    return x + x;
endfunction

export double;

endpackage
