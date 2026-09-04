// A submodule special output that the parent never uses, which is the
// case wireMapA_out has to handle without naming it.
//
// AConv builds an "<inst>$<port>" wire id only for a submodule output
// clock, gate, reset or inout that the design references.  This module
// leaves the gated clock's output unused, so no such id exists, and
// the deduction must read the port's properties off the VModInfo
// rather than construct the name -- constructing it would intern a
// backend name before the Verilog backend runs, and identifier order
// in bsc is interning order.
//
// The pass method drives an output port straight from a module
// argument, which is what forces the deduction to consult the map at
// all: it is reached from getOutPropsA's ASPort case.
//
// (APkgProps_SubClock covers the referenced case, where the wires do
// come from a submodule's special outputs.)

import Clocks::*;

interface APkgProps_UnusedSubClock;
   method Bit#(8) pass();
endinterface

(* synthesize *)
module sysAPkgProps_UnusedSubClock #(Bit#(8) inp) (APkgProps_UnusedSubClock);
   Clock clk <- exposeCurrentClock;
   GatedClockIfc g <- mkGatedClock(True, clk);
   Reg#(Bool) cond <- mkReg(False);

   rule gate;
      g.setGateCond(cond);
      cond <= !cond;
   endrule

   method Bit#(8) pass() = inp;
endmodule
