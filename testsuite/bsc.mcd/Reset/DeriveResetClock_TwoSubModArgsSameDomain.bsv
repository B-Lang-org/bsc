import Clocks :: *;

(* synthesize *)
module sysDeriveResetClock_TwoSubModArgsSameDomain#(Reset rst)();

   // make a clock in the same family
   GatedClockIfc i <- mkGatedClockFromCC(True);

   Reg#(Bool) r1 <- mkReg(True, reset_by rst);
   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by i.new_clk);

endmodule
