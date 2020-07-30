(* synthesize *)
module sysRuleNameNonAlphanum1 ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule \r+1 ;
      rg <= rg + 2;
   endrule

   (* descending_urgency = "\\r+1 , r2" *)
   rule r2;
      rg <= rg + 1;
   endrule

endmodule

