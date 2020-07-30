import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_NoReset_WrongReset ();

   Reset rst2 <- mkInitialReset(2);
   
   Reg#(Bit#(32)) x <- mkReg(0, reset_by rst2);

   Empty i <- mkModulePort_ParentUse_NoReset_WrongReset_Sub (x);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_NoReset_WrongReset_Sub
            ( (* reset_by="no_reset" *)
	      Bit#(32) x,
	      Empty i
	    );

   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= x;
   endrule
endmodule
