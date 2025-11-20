

(* synthesize *)
module sysModulePort_ParentUse_NoReset_RightReset ();
   Empty i <- mkModulePort_ParentUse_NoReset_RightReset_Sub (17);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_NoReset_RightReset_Sub
            ( (* reset_by="no_reset" *)
	      Bit#(32) x,
	      Empty i
	    );

   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= x;
   endrule
endmodule
