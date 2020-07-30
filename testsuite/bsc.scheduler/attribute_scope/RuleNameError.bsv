
(* synthesize *)
module sysRuleNameError ();

   (* descending_urgency = "r1, badname" *)
   rule r1;
      $display("r1");
   endrule

   // Non-rule statement, so that the rules are in separate addRules blocks
   Bool b1 = True;

   // The user should not continue to see errors each time a new rule is added
   rule r2;
      $display("r2");
   endrule

   Bool b2 = True;

   rule r3;
      $display("r3");
   endrule
endmodule

