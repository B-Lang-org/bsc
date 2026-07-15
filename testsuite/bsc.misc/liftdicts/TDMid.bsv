package TDMid;
import TCBase::*;
import TDBase::*;

// TD#(Maybe#(Bool)) evidence: the (sole) TD instance applied to the
// GENERAL TC evidence.
function Bit#(8) dmid(Maybe#(Bool) x) = dtag(x);

endpackage
