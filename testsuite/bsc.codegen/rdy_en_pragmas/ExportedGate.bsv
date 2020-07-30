import Clocks::*;

(* synthesize *)
module sysExportedGate(Reg#(Bool));
   GatedClockIfc g <- mkGatedClockFromCC(True);

   Reg#(Bool) rg <- mkReg(True, clocked_by g.new_clk);

   return (rg);
endmodule

