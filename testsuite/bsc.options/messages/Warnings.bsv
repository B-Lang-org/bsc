// Generate four warnings:
//
// (1) Arbitrary earliness warning (G0036)
// (2) Action shadowing warning (G0117)
// (3) Arbitrary urgency warning (G0010)
// (4) System task in method warning (G0020)
//

interface Ifc;
   method Action m1();
   method Action m2();
endinterface

(* synthesize *)
module sysWarnings (Ifc);
   Reg#(Bool) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU;
   Reg#(Bool) rg3 <- mkRegU;

   // These rules have arbitrary earliness, and one shadows the other
   rule r1;
      rg1 <= True;
   endrule
   rule r2;
      rg1 <= False;
   endrule

   // This rule and method have arbitrary urgency
   rule r3;
      rg2 <= rg3;
   endrule
   method Action m1();
      rg3 <= rg2;
   endmethod

   // This method contains a system task
   method Action m2();
      $display("m2");
   endmethod
endmodule

