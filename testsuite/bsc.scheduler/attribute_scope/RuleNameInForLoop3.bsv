import Vector::*;

(* synthesize *)
module sysRuleNameInForLoop3();
   Vector#(4, Reg#(UInt#(16))) rg <- replicateM(mkRegU);

   for (Integer i = 0; i < 4; i = i + 1) begin
      rule r1;
         $display("r1");
      endrule

      rule r2;
         rg[i] <= rg[i] + 1;
         $display("r2");
      endrule

      // By putting a non-rule statement here, we break them into two blocks
      Bool b = True;

      rule r3;
         $display("r3");
      endrule

      // Because there is no "r2" in this block, the attribute will refer
      // to a rule by that name already added to the module.  That means
      // that later iterations will refer to "r2" from the first iteration,
      // not the "r2" from the current iteration.
      //
      (* descending_urgency = "r2, r4" *)
      rule r4;
         rg[i] <= rg[i] + 2;
         $display("r4");
      endrule
   end
endmodule
