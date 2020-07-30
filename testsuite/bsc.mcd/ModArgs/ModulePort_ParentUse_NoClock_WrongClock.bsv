import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_NoClock_WrongClock ();

   Clock clk2 <- mkAbsoluteClock(7,15);
   
   Reg#(Bit#(32)) x <- mkRegU(clocked_by clk2);

   Empty i <- mkModulePort_ParentUse_NoClock_WrongClock_Sub (x);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_NoClock_WrongClock_Sub
            ( (* clocked_by="no_clock" *)
	      Bit#(32) x,
	      Empty i
	    );

   Reg#(Bit#(32)) rg <- mkRegU();

   rule r;
      rg <= x;
   endrule
endmodule
