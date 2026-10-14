// Test: Function/variable reference (Phase 2)
// Expected: NO warning - Helper is used via function call

package FunctionReference;

import Helper::*;

function Byte test();
    return addOne(5);  // Calls function from Helper
endfunction

endpackage
