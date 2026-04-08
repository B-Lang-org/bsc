package ATFQualifiedBSV;

// Test that when two imported files each define an ATF named Elem,
// both can be referenced using qualified names (BSV syntax).

import ATFQualifiedLib1 :: *;
import ATFQualifiedLib2 :: *;

// Use qualified names to disambiguate the two Elem type functions.
function ATFQualifiedLib1::Elem#(ATFQualifiedLib1::Box#(Integer))
    test1(ATFQualifiedLib1::Box#(Integer) b) = extract(b);

function ATFQualifiedLib2::Elem#(ATFQualifiedLib2::Tag#(Bool))
    test2(ATFQualifiedLib2::Tag#(Bool) t) = unwrap(t);

endpackage
