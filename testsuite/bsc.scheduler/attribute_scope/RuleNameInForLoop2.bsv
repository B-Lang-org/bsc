import Vector::*;

(* synthesize *)
module sysRuleNameInForLoop2();
   Vector#(4, Reg#(UInt#(16))) rg <- replicateM(mkRegU);

   for (Integer i = 0; i < 4; i = i + 1) begin
      rule r1;
         $display("r1");
      endrule

      // This fails in the first iteration, because it refers to "r4"
      // which has not been added yet and is not in this block (because
      // the "r4" rule below is in a separate rules block)
      //
      (* descending_urgency = "r2, r4" *)
      rule r2;
         rg[i] <= rg[i] + 1;
         $display("r2");
      endrule

      // By putting a non-rule statement here, we break them into two blocks
      Bool b = True;

      rule r3;
         $display("r3");
      endrule

      rule r4;
         rg[i] <= rg[i] + 2;
         $display("r4");
      endrule
   end
endmodule
