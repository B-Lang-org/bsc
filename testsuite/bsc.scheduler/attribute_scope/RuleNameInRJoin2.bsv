
(* synthesize *)
module sysRuleNameInRJoin2 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   Rules rs1 =
      rules
         (* descending_urgency = "r1, r2" *)
         rule r1;
            rg <= rg + 1;
         endrule
      endrules;

   Rules rs2 =
      rules
         rule r2;
            rg <= rg + 2;
         endrule
      endrules;

   Rules rs3 =
      rules
         rule r3;
            rg <= rg + 3;
         endrule
      endrules;

   addRules(rJoin(rs2, rJoin(rs1, rs3)));
endmodule

