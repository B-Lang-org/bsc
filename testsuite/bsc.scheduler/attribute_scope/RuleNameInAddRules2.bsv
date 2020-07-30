(* synthesize *)
module sysRuleNameInAddRules2 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r1;
      rg <= rg + 1;
   endrule

   Rules rs =
      rules
         (* descending_urgency = "r1, r2" *)
         rule r2;
            rg <= rg + 2;
         endrule
      endrules;

   // Give an instance name
   let a <- addRules(rs);
endmodule

