// Scale test for Verilog generation of foreign-block-inlined defs.
//
// A rule feeds the result of an ActionValue system task ($stime) through
// a large body of defs (an 8192-element Vector, reduced by two folds)
// into a final system task.  Every one of those defs is inlined into the
// negedge foreign block and declared "reg".  A compact source elaborates
// to tens of thousands of such defs.
//
// The def selection (vForeignBlock) and reg-marking (AVerilog) once used
// per-def list-membership tests, making Verilog generation quadratic in
// the number of foreign-block defs; at this scale that took about 9 of
// the compile's 21 seconds.  With the Set-based membership tests it is
// roughly linear (about 1 second).  The test has no time limit, so it
// checks the generated Verilog and its output at this scale rather than
// the timing.

import Vector::*;

typedef 8192 NLEAF;

function Bit#(32) leaf(Bit#(32) t, Integer i);
   return (t + fromInteger(i)) ^ (t >> (i % 31 + 1));
endfunction

(* synthesize *)
module mkForeignInlineLarge(Empty);
   Reg#(Bit#(32)) acc <- mkReg(0);
   rule r;
      let t <- $stime;
      Vector#(NLEAF, Bit#(32)) xs = genWith(leaf(truncate(t)));
      Bit#(32) a = fold( \^ , xs);
      Bit#(32) b = fold( \+ , xs);
      $display("%d %d", a, b);
      acc <= acc + 1;
      if (acc == 2) $finish(0);
   endrule
endmodule
