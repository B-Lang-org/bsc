import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_NoClock_RightClock ();
   Empty i <- mkModulePort_ParentUse_NoClock_RightClock_Sub (17);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_NoClock_RightClock_Sub
            ( (* clocked_by="no_clock" *)
	      Bit#(32) x,
	      Empty i
	    );

   Reg#(Bit#(32)) rg <- mkRegU();

   rule r;
      rg <= x;
   endrule
endmodule
