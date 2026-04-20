// Test: orphan instance used ONLY via a proviso resolved during ctxReduce.
// ctxReduce resolves Describable#(Bool) from the instance proviso, recording
// BoolDescribable in that TI run - but cCtxReduceIO discards tsUsedPackages.
// The converted instance body never calls describe(Bool), so cTypeCheck does
// not re-resolve the predicate.  BoolDescribable should NOT get T0157.

package ProvisoDrop;

import Helper::*;
import BoolDescribable::*;  // Orphan Describable#(Bool)

typedef struct { Bool val; } BoolWrapper deriving (Bits);

// Concrete proviso Describable#(Bool): ctxReduce resolves it via BoolDescribable.
// Body does NOT call describe on a Bool, so there is no cTypeCheck re-resolution.
instance Describable#(BoolWrapper) provisos(Describable#(Bool));
    function String describe(BoolWrapper w) = "bool-wrapper";
endinstance

endpackage
