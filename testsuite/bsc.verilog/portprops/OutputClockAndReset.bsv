import Clocks :: *;

interface Ifc;
   interface Clock clk_out;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysOutputClockAndReset (Ifc);
   Clock c <- mkAbsoluteClock (10, 20);
   GatedClockIfc g <- mkGatedClock(True, c);
   Reset r <- mkInitialReset(2, clocked_by c);

   interface Clock clk_out = g.new_clk;
   interface Reset rst_out = r;
endmodule

