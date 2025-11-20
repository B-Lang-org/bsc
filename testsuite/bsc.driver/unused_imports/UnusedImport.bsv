// Test: Basic unused import (BSV syntax)
// Expected: Warning about Helper being unused

package UnusedImport;

import Helper::*;  // Not used - should warn
import Vector::*;  // Used

function Bit#(8) test();
    Vector#(3, Bit#(8)) v = replicate(0);
    return v[0];
endfunction

endpackage
