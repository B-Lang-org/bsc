// Test: Re-export data type with constructors (Phase 3)
// Expected: NO warning - Helper is used because we re-export Color

package ReexportData;

import Helper::*;

// Re-export Color data type with all constructors
export Color(..);

endpackage
