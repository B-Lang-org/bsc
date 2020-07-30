module mkSub (Reg#(UInt#(16)) rg1, Reg#(UInt#(16)) rg2, Empty ifc);
   (* descending_urgency = "sub_r, r" *)
   rule sub_r;
      rg1 <= rg1 + 2;
      rg2 <= rg2 + 2;
   endrule
endmodule

(* synthesize *)
module sysRuleNameInSubmodClash ();
   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   rule r;
      rg1 <= rg1 + 1;
   endrule

   rule s_r;
      rg2 <= rg2 + 1;
   endrule

   Empty s <- mkSub(rg1, rg2);
endmodule

