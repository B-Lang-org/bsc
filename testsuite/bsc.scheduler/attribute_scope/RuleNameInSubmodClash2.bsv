module mkSub (Reg#(UInt#(16)) rg1, Empty ifc);
   Reg#(UInt#(16)) rg2 <- mkRegU;

   rule r1;
      rg2 <= rg2 + 1;
   endrule   

   // Put a non-rule statement here to break up the rules
   Reg#(UInt#(16)) rg3  <- mkRegU;

   // This should refer to the rule above,
   // even if it shares the same name as an already instantiated rule
   // and was renamed (the attribute should then also be renamed)
   //
   (* descending_urgency = "r1, r2" *)
   rule r2;
      rg1 <= rg1 + 2;
      rg2 <= rg2 + 2;
   endrule
endmodule

(* synthesize *)
module sysRuleNameInSubmodClash2 ();
   Reg#(UInt#(16)) rg1 <- mkRegU;

   rule r1;
      rg1 <= rg1 + 1;
   endrule

   mkSub(rg1);
endmodule

