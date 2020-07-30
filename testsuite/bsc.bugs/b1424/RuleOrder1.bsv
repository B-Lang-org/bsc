// We expect the rules to schedule in the order they are elaborated
// (set_r3, set_r1, set_r2, done).

import Clocks::*;

(* synthesize *)
module sysRuleOrder1();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   rule set_r3;
     rg3 <= !rg3;
     $display("Changing r3");
   endrule

   rule set_r1;
     rg1 <= !rg1;
     $display("Changing r1");
   endrule

   rule set_r2;
     rg2 <= !rg2;
     $display("Changing r2");
   endrule

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule
