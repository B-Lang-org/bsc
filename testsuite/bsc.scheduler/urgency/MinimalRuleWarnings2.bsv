// Test that we aren't suppressing too many urgency warnings.
// This should issue three warnings.  If the descending urgency
// attribute is added, it should issue two.

(* synthesize *)
module mkMinimalRuleWarnings2 ();
   Reg#(Bit#(8)) rg1 <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;
   Reg#(Bit#(8)) rg3 <- mkRegU;

   //(* descending_urgency = "r3,r4" *)
   rule r4;
      rg1 <= rg1 - 1;
      rg2 <= rg2 - 1;
      rg3 <= rg3 - 1;
   endrule

   rule r3;
      rg3 <= rg3 + 1;
   endrule

   rule r2;
      rg2 <= rg2 + 1;
   endrule

   rule r1;
      rg1 <= rg1 + 1;
   endrule

endmodule
