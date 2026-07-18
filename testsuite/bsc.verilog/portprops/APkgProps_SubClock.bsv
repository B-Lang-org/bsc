// Test the APackage-based VIOProps deduction (getIOPropsA) for
// output clock, gate, and reset ports whose wires come from a
// submodule's special outputs (a gated clock generator and a reset
// generator), rather than from the module's own inputs.

import Clocks::*;

interface APkgProps_SubClock;
   interface Clock cOut;
   interface Reset rOut;
endinterface

(* synthesize *)
module sysAPkgProps_SubClock (APkgProps_SubClock);
   Clock clk <- exposeCurrentClock;
   GatedClockIfc g <- mkGatedClock(True, clk);
   Reg#(Bool) b <- mkRegU;

   rule flip;
      b <= !b;
      g.setGateCond(b);
   endrule

   MakeResetIfc mr <- mkReset(2, True, g.new_clk);

   interface cOut = g.new_clk;
   interface rOut = mr.new_rst;
endmodule
