module mkBuildMod (Reg#(UInt#(16)) rg1, Reg#(UInt#(16)) rg2, Bool b);
   (* descending_urgency = "sub_r, r" *)
   rule sub_r;
      rg1 <= rg1 + 2;
      rg2 <= rg2 + 2;
   endrule

   return True;
endmodule

(* synthesize *)
module sysRuleNameInBuildModClash ();
   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;

   Reg#(UInt#(16)) rg1 <- mkRegU;
   Reg#(UInt#(16)) rg2 <- mkRegU;

   rule r;
      rg1 <= rg1 + 1;
   endrule

   rule s_r;
      rg2 <= rg2 + 1;
   endrule

   // Break up the rule blocks, so that the rules are guaranteed to
   // already be added to the module monad
   Bool b1 = True;

   rule r2;
      let b2 = primBuildModule(primGetName(s), clk, rst, mkBuildMod(rg1, rg2));
      $display(b1 && b2);
   endrule
endmodule

