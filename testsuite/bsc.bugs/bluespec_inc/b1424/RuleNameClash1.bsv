// We expect the rules to schedule in the order they are elaborated
// in the synthesized module, without regard to clashing names in other
// modules which perturb the string internment order. (r2, r1, done)

import Clocks::*;

(* synthesize *)
module mkRuleNameClash_OtherMod();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);

   rule r1;
     rg1 <= !rg1;
     $display("Changing r1");
   endrule

   rule r2;
     rg2 <= !rg2;
     $display("Changing r2");
   endrule

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule

(* synthesize *)
module sysRuleNameClash1();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);

   rule r2;
     rg2 <= !rg2;
     $display("Changing r2");
   endrule

   rule r1;
     rg1 <= !rg1;
     $display("Changing r1");
   endrule

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule
