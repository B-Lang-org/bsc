
(* synthesize *)
module sysRuleNameErrorJoin ();

   Rules rs1 =
      rules
         (* descending_urgency = "r1, badname" *)
         rule r1;
            $display("r1");
         endrule
      endrules;

   Rules rs2 =
      rules
         rule r2;
            $display("r2");
         endrule
      endrules;

   Rules rs3 =
      rules
         rule r3;
            $display("r3");
         endrule
      endrules;

   // The user should not continue to see errors each time a new rule is added
   addRules(rJoin(rs3, rJoin(rs2, rs1)));

endmodule

