
(* synthesize *)
module sysRuleNameInModule1 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r;
      rg <= rg + 1;
   endrule

   module mkSub ();
      (* descending_urgency = "sub_r, r" *)
      rule sub_r;
         rg <= rg + 2;
      endrule
   endmodule

   Empty s <- mkSub;
endmodule

