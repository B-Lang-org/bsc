// Two different hierarchies that both instantiate mkSub from SharedSub,
// at different depths:
//   mkTop  -> mkSub             (one level)
//   mkTop2 -> mkMid -> mkSub    (two levels)
// The per-module C++ generated for mkSub must be identical in both, since
// the whole point of per-module codegen (-c) is that a module's C++ does not depend
// on the surrounding hierarchy.
package Hier;

import SharedSub::*;

(* synthesize *)
module mkMid(Counter);
  Counter c <- mkSub;
  method Action inc(); c.inc(); endmethod
  method Bit#(8) value(); return c.value(); endmethod
endmodule

(* synthesize *)
module mkTop();
  Counter c <- mkSub;
  Reg#(Bit#(8)) n <- mkReg(0);
  rule go;
    c.inc();
    n <= n + 1;
    if (n == 5) begin $display("v=%0d", c.value()); $finish(0); end
  endrule
endmodule

(* synthesize *)
module mkTop2();
  Counter c <- mkMid;
  Reg#(Bit#(8)) n <- mkReg(0);
  rule go;
    c.inc();
    n <= n + 1;
    if (n == 5) begin $display("v=%0d", c.value()); $finish(0); end
  endrule
endmodule

endpackage
