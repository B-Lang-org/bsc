import Clocks::*;

(* synthesize *)
module mkModulePort_ClockMux #(Bool b)();

   Clock clk1 <- exposeCurrentClock;
   Clock clk2 <- mkAbsoluteClock(7,15);

   let clk = b ? clk1 : clk2;

   Reg#(Bit#(32)) x <- mkReg(0, clocked_by clk, reset_by noReset);

   rule r;
      x <= x + 1;
      $display("X = ", x);
      if (x > 17)
	 $finish(0);
   endrule

endmodule

