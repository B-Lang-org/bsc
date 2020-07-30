
(* synthesize *)
module sysRuleNameInRJoin1 ();
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

   addRules(rJoin(rs1, rs2));
endmodule

