module mkBuildMod (Reg#(UInt#(16)) rg, Bool b);
   (* descending_urgency = "sub_r, r" *)
   rule sub_r;
      rg <= rg + 2;
   endrule

   return True;
endmodule

(* synthesize *)
module sysRuleNameInBuildMod ();
   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;

   Reg#(UInt#(16)) rg <- mkRegU;

   rule r;
      rg <= rg + 1;
   endrule

   // Break up the rule blocks, so that "r" is guaranteed to already be
   // added to the module monad
   Bool b1 = True;

   rule r2;
      let b2 = primBuildModule(primGetName(s), clk, rst, mkBuildMod(rg));
      $display(b1 && b2);
   endrule
endmodule

