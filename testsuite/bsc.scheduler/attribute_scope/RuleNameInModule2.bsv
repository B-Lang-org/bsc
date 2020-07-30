
(* synthesize *)
module sysRuleNameInModule2 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   module mkSub ();
      (* descending_urgency = "sub_r, r" *)
      rule sub_r;
         rg <= rg + 2;
      endrule
   endmodule

   rule r;
      rg <= rg + 1;
   endrule

   Empty s <- mkSub;
endmodule

