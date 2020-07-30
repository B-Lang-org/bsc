import Clocks :: *;

(* synthesize *)
module sysDeriveResetClock_BoundaryClockInSameFamily#(Clock c, Reset rst_in)();

   // make a clock in the same family, which is not exported
   GatedClockIfc ci <- mkGatedClock(True, c);

   // use the input reset with the new clock
   Reg#(Bool) rg <- mkReg(True, clocked_by ci.new_clk, reset_by rst_in);

endmodule
