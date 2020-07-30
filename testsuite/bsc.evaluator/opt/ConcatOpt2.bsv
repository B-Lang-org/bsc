// Test optimization of PrimAnd, PrimOr, PrimXOr operations on concats,
// constants, and undefs.  Expressions like this:
//    { e1, e2 } op { e3, e4 }
// can turn into this:
//    { (e1 op e3), (e2 op e4) }
// if the expressions are of the same length.  Constants ands undefs can
// be split:
//    { e1, e2 } op { c1, c2 }
// can become:
//    { (e1 op {c1, c2[..]}), (e2 op c2[..]) }
// And nested concats can be re-ordered etc.

import Vector::*;

(* synthesize *)
module sysConcatOpt2();

   Reg#(Bit#(8)) counter <- mkReg(0);

   Reg#(Vector#(3,Maybe#(Bit#(15)))) rg <- mkRegU;

   rule do_test;
      counter <= counter + 1;
      case (counter)
         0 : begin
	        rg <= replicate(Invalid);
	     end
         1 : begin
	        $display("rg = %h", rg);
	     end
         default: $finish(0);
      endcase
   endrule

endmodule

