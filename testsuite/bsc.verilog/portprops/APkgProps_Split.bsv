// Test that the APackage-based VIOProps deduction (getIOPropsA)
// recognizes the boolean reductions that the netlist optimization
// performs: the ready of a split method is the OR of the two
// complementary split conditions, a tautology, so RDY_toggle is
// "const" in both dumps.

interface APkgProps_Split;
   method Action toggle(Bool c);
endinterface

(* synthesize *)
module sysAPkgProps_Split (APkgProps_Split);
   Reg#(Bit#(8)) r1 <- mkRegU;
   Reg#(Bit#(8)) r2 <- mkRegU;

   method Action toggle(Bool c);
      (* split *)
      if (c)
         r1 <= 1;
      else
         r2 <= 2;
   endmethod
endmodule
