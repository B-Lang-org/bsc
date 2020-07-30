
(* synthesize *)
module sysRuleNameInModule3 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   module mkSub ();
      rule sub_r;
         rg <= rg + 2;
      endrule
   endmodule

   (* descending_urgency = "sub_r, r" *)
   rule r;
      rg <= rg + 1;
   endrule

   Empty s <- mkSub;

endmodule

