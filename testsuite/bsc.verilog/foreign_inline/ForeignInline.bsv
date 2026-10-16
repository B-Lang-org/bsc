// A module whose rule takes the result of an ActionValue system task
// ($stime) through a body of defs (a Vector fold) before another system
// task consumes it.  Those defs are inlined into the negedge foreign
// block (declared "reg", assigned in the always block).  This exercises
// the def selection and reg-marking in vForeignBlock / AVerilog, whose
// per-def membership tests were quadratic in the number of such defs.

import Vector::*;

function Bit#(32) leaf(Bit#(32) t, Integer i);
   return (t + fromInteger(i)) ^ (t >> (i % 15 + 1));
endfunction

(* synthesize *)
module mkForeignInline(Empty);
   Reg#(Bit#(32)) acc <- mkReg(0);
   rule r;
      let t <- $stime;
      Vector#(8, Bit#(32)) xs = genWith(leaf(t));
      Bit#(32) a = fold( \^ , xs);
      Bit#(32) b = fold( \+ , xs);
      $display("%d %d", a, b);
      acc <= acc + 1;
      if (acc == 2) $finish(0);
   endrule
endmodule
