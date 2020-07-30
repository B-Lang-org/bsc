import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_TwoResets ();

   Reset rst1 <- exposeCurrentReset;
   Reset rst2 <- mkInitialReset(2);
   
   Reg#(Bit#(32)) x <- mkReg(0, reset_by rst1);
   Reg#(Bit#(32)) y <- mkReg(0, reset_by rst2);
   
   Empty i <- mkModulePort_ParentUse_TwoResets_Sub (x+y);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_TwoResets_Sub #(Bit#(32) x) ();
   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= x;
   endrule
endmodule
