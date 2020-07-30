import Vector::*;

// Test that the "parameter" attribute is preserved even though the arg
// is split into pieces.
// 
(* synthesize *)
module sysVecParam #(parameter Vector#(4, Bool) bs) ();
   Reg#(Vector#(4, Bool)) rg <- mkReg(bs);
endmodule

