
(* synthesize *)
module sysRuleNameAcrossTopModule ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r1;
      rg <= rg + 1;
   endrule

   // Non-rule statement, so that the rules are in separate addRules blocks
   UInt#(16) v_rg = rg;

   (* descending_urgency = "r1, r2" *)
   rule r2;
      rg <= v_rg + 2;
   endrule
endmodule

