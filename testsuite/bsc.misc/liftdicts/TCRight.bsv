package TCRight;
import TCBase::*;

// The right arm of the diamond defines the specific orphan instance
// and uses it.
instance TC#(Maybe#(Bool));
   function tag(x) = 8'd2;
endinstance

function Bit#(8) rightTag(Maybe#(Bool) x) = tag(x);

endpackage
