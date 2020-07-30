module mkBottom (Reg#(UInt#(16)) rg2, Empty ifc);
   rule r1;
      rg2 <= rg2 + 2;
   endrule
endmodule

module mkMiddle (Reg#(UInt#(16)) rg1, Empty ifc);
   Reg#(UInt#(16)) rg2 <- mkRegU;

   Empty b <- mkBottom(rg2);

   // This should refer to the rule in the child, not the parent
   (* descending_urgency = "r2, b_r1" *)
   rule r2;
      rg1 <= rg1 + 1;
      rg2 <= rg2 + 1;
   endrule
endmodule

(* synthesize *)
module sysRuleNameInParent ();
   Reg#(UInt#(16)) rg1 <- mkRegU;

   rule m_b_r1;
      rg1 <= rg1 + 2;
   endrule

   Empty m <- mkMiddle(rg1);
endmodule
