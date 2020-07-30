
(* synthesize *)
module sysRuleNameAcrossSubModule2 ();
   Empty m <- mkMid;
endmodule

module mkMid();
   Empty b <- mkBottom;
endmodule

module mkBottom();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r1;
      rg <= rg + 1;
   endrule

   // Non-rule statement, so that the rules are in separate addRules blocks
   //
   // Make it a submodule, to test that pushing and popping a subscope
   // doesn't interfere
   //
   Empty s <- mkSub();

   (* descending_urgency = "r1, r2" *)
   rule r2;
      rg <= rg + 2;
   endrule
endmodule

module mkSub();
   rule r3;
      $display("r3");
   endrule
endmodule

