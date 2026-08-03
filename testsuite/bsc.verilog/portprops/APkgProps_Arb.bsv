// Test that the APackage-based VIOProps deduction (getIOPropsA)
// models the argument muxes of state instance methods using the
// schedule (port allocation, exclusivity, and earliness order):
// both methods are always_enabled, so both callers of val._write and
// res._write have constant-1 WILL_FIREs, and the priority mux folds
// to the more urgent caller -- start's arguments become direct
// connections to the registers ("reg"), and check's write loses the
// arbitration.

(* always_enabled *)
interface APkgProps_Arb;
   method Action start(Bit#(6) a, Bit#(6) b);
   method ActionValue#(Bit#(6)) check(Bit#(6) d);
endinterface

(* synthesize *)
module sysAPkgProps_Arb (APkgProps_Arb);
   Reg#(Bit#(6)) val <- mkReg(0);
   Reg#(Bit#(6)) res <- mkReg(0);

   method Action start(Bit#(6) a, Bit#(6) b);
      val <= a;
      res <= b;
   endmethod

   method ActionValue#(Bit#(6)) check(Bit#(6) d);
      val <= val + 1;
      res <= res + 2;
      return res + d;
   endmethod
endmodule
