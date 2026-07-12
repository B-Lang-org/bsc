// Test: orphan instance used when class comes from a different import
// Expected: NO warning - BoolDescribable is used via orphan instance resolution
//
// Key difference from OrphanInstanceUse: the class (Describable) comes from
// Helper, not from BoolDescribable.  So BoolDescribable can only be justified
// by the orphan instance match, not by a class or symbol lookup.

package UseOrphanSeparately;

import Helper::*;          // Has Describable class + Describable#(Byte) instance
import BoolDescribable::*; // Has orphan Describable#(Bool) instance ONLY

function String test();
    Bool b = True;
    return describe(b);  // Uses orphan instance from BoolDescribable
endfunction

endpackage
