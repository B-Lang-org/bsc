(* synthesize *)
module sysRuleNameNonAlphanumClash1 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r1;
      rg <= rg + 2;
   endrule

   rule \r-1 ;
      rg <= rg + 1;
   endrule

endmodule

