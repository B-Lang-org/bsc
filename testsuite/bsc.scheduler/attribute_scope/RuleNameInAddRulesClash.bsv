(* synthesize *)
module sysRuleNameInAddRulesClash ();
   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   rule a_r;
      rg1 <= rg1 + 1;
   endrule

   Rules rs =
      rules
         rule r;
            rg2 <= rg2 + 1;
         endrule

         (* descending_urgency = "r, r2" *)
         rule r2;
            rg1 <= rg1 + 2;
            rg2 <= rg2 + 2;
         endrule
      endrules;

   // Give an instance name
   let a <- addRules(rs);
endmodule

