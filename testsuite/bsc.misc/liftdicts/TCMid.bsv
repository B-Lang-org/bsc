package TCMid;
import TCBase::*;

// Forces a lifted coherent dictionary for TC#(Maybe#(Bool)) in this
// package, built from the only instance visible here: the general one.
function Bit#(8) midTag(Maybe#(Bool) x) = tag(x);

endpackage
