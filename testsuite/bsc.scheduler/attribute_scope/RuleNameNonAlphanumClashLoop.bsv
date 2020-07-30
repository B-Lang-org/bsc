import Vector ::*;

(* synthesize *)
module sysRuleNameNonAlphanumClashLoop ();
   Vector#(2, Reg#(UInt#(16))) rg <- replicateM(mkRegU);

   for (Integer i=0; i<2; i=i+1) begin
      rule r1;
         rg[i] <= rg[i] + 2;
      endrule

      rule \r-1 ;
         rg[i] <= rg[i] + 1;
      endrule
   end

endmodule

