import Vector::*;

(* synthesize *)
module sysRuleNameInForLoop1();
   Vector#(4, Reg#(UInt#(16))) rg <- replicateM(mkRegU);

   for (Integer i = 0; i < 4; i = i + 1) begin
      rule r1;
         $display("r1");
      endrule

      // This refers to r4 in this iteration
      // because they are all in one rules block
      (* descending_urgency = "r2, r4" *)
      rule r2;
         rg[i] <= rg[i] + 1;
         $display("r2");
      endrule

      rule r3;
         $display("r3");
      endrule

      rule r4;
         rg[i] <= rg[i] + 2;
         $display("r4");
      endrule
   end
endmodule
