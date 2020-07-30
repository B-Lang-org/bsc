import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUse_WrongClock ();

   Clock clk2 <- mkAbsoluteClock(7,15);
   
   Reg#(Bit#(32)) x <- mkRegU(clocked_by clk2);

   Empty i <- mkModulePort_ParentUse_WrongClock_Sub (x, clk2);
endmodule

(* synthesize *)
module mkModulePort_ParentUse_WrongClock_Sub #(Bit#(32) x)
                                              (Clock c2, Empty i);
   // this should be clocked_by c2
   Reg#(Bit#(32)) rg <- mkRegU();

   rule r;
      rg <= x;
   endrule
endmodule
