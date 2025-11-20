// Test: Ambiguous constructor disambiguation (Phase 2)
// Expected: Warning about Helper2 being unused
//           Helper should be used (Red is disambiguated by function argument type)

package AmbiguousConstructor;

import Helper::*;   // Has Color with Red constructor - used via Helper3.isRed
import Helper2::*;  // Also has Color with Red constructor - NOT used
import Helper3::*;  // Has isRed function expecting Helper::Color

// Red is ambiguous (could be Helper.Color.Red or Helper2.Color.Red)
// but isRed expects Helper::Color, so Red is disambiguated to Helper.Color.Red
function Bool test();
    return isRed(Red);  // Red disambiguated to Helper.Color.Red by isRed's parameter type
endfunction

endpackage
