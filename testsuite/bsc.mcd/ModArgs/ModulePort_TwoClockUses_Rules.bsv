import Clocks::*;

(* synthesize *)
module sysModulePort_TwoClockUses_Rules #(Bit#(32) x)
                                         (Clock c2, Reset r2, Empty i);

   Reg#(Bit#(32)) rg1 <- mkReg(0);

   Reg#(Bit#(32)) rg2 <- mkReg(0, clocked_by c2, reset_by r2);

   rule r1;
      rg1 <= x;
   endrule

   rule r2;
      rg2 <= x;
   endrule

endmodule
