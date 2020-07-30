import Clocks::*;

interface Ifc;
   method Action m();
endinterface

(* synthesize *)
module sysModulePort_TwoClockUses_RuleMethod #(Bit#(32) x)
                                              (Clock c2, Reset r2, Ifc i);

   Reg#(Bit#(32)) rg1 <- mkReg(0);

   Reg#(Bit#(32)) rg2 <- mkReg(0, clocked_by c2, reset_by r2);

   rule r;
      rg1 <= x;
   endrule

   method Action m();
      rg2 <= x;
   endmethod

endmodule
