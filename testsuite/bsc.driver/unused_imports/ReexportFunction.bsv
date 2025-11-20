// Test: Re-export function (Phase 3)
// Expected: NO warning - Helper is used because we re-export addOne

package ReexportFunction;

import Helper::*;

// Re-export the addOne function
export addOne;

endpackage
