// Test: Re-export (Phase 3)
// Expected: NO warning - Helper is re-exported

package Reexport;

import Helper::*;

// Re-export everything from Helper
export Helper::*;

endpackage
