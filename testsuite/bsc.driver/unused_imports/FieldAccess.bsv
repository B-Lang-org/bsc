// Test: Field access (Phase 2)
// Expected: NO warning - Helper is used via field access

package FieldAccess;

import Helper::*;

function Byte getX(Point p);
    return p.x;  // Accesses field from Helper's Point struct
endfunction

endpackage
