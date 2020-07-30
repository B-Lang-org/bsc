import Clocks :: *;

(* synthesize *)
module sysCheckResetClockPass2 (Empty);
   // make a clock in the same family
   GatedClockIfc i <- mkGatedClockFromCC(True);

   Reg#(Bool) r1 <- mkReg(True);
   Reg#(Bool) r2 <- mkReg(True, clocked_by i.new_clk);

endmodule
