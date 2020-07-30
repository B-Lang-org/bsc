import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_TwoClocks ();

   Clock clk1 <- exposeCurrentClock;
   Reset rst1 <- exposeCurrentReset;

   Clock clk2 <- mkAbsoluteClock(7,15);
   Reset rst2 <- mkInitialReset(2, clocked_by clk2);
   
   Reg#(Bit#(32)) x <- mkReg(0, clocked_by clk1, reset_by rst1);
   Reg#(Bit#(32)) y <- mkReg(0, clocked_by clk2, reset_by rst2);
   
   Empty i <- mkModulePort_ParentUse_TwoClocks_Sub (x+y, clk2);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_TwoClocks_Sub #(Bit#(32) x) (Clock c2, Empty i);
   Reg#(Bit#(32)) rg <- mkReg(0);

   rule r;
      rg <= x;
   endrule
endmodule
