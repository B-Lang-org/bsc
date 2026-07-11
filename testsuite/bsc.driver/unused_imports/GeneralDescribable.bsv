package GeneralDescribable;

import Helper::*;

// General instance that matches any type.  Used by incoherence tests:
// when BoolDescribable is also in scope, resolving Describable#(a) for
// a free type variable makes this instance match incoherently.
instance Describable#(a);
    function String describe(a x) = "generic";
endinstance

endpackage
