import Clocks :: *;

interface Ifc;
   interface Reset rst_out;
   interface Clock clk_out;
endinterface

(* synthesize *)
module sysOutputReset_BoundaryClockInSameFamily (Ifc);

   // make a new clock, which is not exported
   Clock c2 <- mkAbsoluteClock (17, 42);

   // make a clock in the same family, which will be exported
   GatedClockIfc ci <- mkGatedClock(True, c2);

   // make a reset sync'd to the unexported clock
   MakeResetIfc ri <- mkReset(2, True, c2);

   // export the reset
   interface rst_out = ri.new_rst;

   // export the clock from the same family
   // (the reset should be associated to this clock,
   //  not get a warning that the specific clock is not exported)
   interface clk_out = ci.new_clk;

endmodule
