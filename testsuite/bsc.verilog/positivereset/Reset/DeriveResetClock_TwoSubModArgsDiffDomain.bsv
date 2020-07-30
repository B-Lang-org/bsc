import Clocks :: *;

(* synthesize *)
module sysDeriveResetClock_TwoSubModArgsDiffDomain#(Clock c2, Reset rst)();

   Reg#(Bool) r1 <- mkReg(True, reset_by rst);
   // c2 is not in the same domain
   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by c2);

endmodule
