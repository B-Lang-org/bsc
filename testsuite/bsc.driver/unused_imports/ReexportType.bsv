// Test: Re-export specific type (Phase 3)
// Expected: NO warning - Helper is used because we re-export Byte

package ReexportType;

import Helper::*;

// Re-export only the Byte type synonym
export Byte;

endpackage
