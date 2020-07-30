(* synthesize *)
module sysRuleNameNonAlphanumClash2 ();
   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   rule r1;
      rg1 <= rg1 + 2;
   endrule

   rule \r-1 ;
      rg2 <= rg2 + 2;
   endrule

   // This attribute should refer to the middle rule
   (* descending_urgency = "\\r-1 , r2" *)
   rule r2;
      rg1 <= rg1 + 1;
      rg2 <= rg2 + 1;
   endrule

endmodule

