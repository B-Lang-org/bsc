// Package with orphan instance (Describable for Bool)
// Both Describable (from Helper) and Bool (from Prelude) are external

package BoolDescribable;

import Helper::*;

// Orphan instance: Describable is from Helper, Bool is from Prelude
instance Describable#(Bool);
    function String describe(Bool b);
        return b ? "true" : "false";
    endfunction
endinstance

// No export of Describable - consumers must import Helper directly

endpackage
