import Clocks :: *;

(* synthesize *)
module sysDeriveResetClock_NoBoundaryClock#(Reset rst)();
   // make a new clock, which is not exported
   Clock c2 <- mkAbsoluteClock (17, 42);

   // use rst with c2
   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by c2);

endmodule
