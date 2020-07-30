import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_WrongReset ();

   Reset rst2 <- mkInitialReset(2);
   
   Reg#(Bit#(32)) x <- mkReg(0, reset_by rst2);

   Empty i <- mkModulePort_ParentUse_WrongReset_Sub (x, rst2);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_WrongReset_Sub #(Bit#(32) x)
                                              (Reset r2, Empty i);
   // this should be reset_by r2
   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= x;
   endrule
endmodule
