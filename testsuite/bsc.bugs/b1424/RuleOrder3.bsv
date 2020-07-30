// We expect the rules to schedule in the order they are elaborated
// (set_r1, set_r2, set_r3, set_r4, set_r5, set_r6, done).

import Clocks::*;

(* synthesize *)
module sysRuleOrder3();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   rule set_r1;
     rg1 <= !rg1;
     $display("Changing r1");
   endrule

   rule set_r2;
     rg2 <= !rg2;
     $display("Changing r2");
   endrule

   rule set_r3;
     rg3 <= !rg3;
     $display("Changing r3");
   endrule

   Reg#(Bool) rg4 <- mkReg(True);

   rule set_r4;
     rg4 <= !rg4;
     $display("Changing r4");
   endrule

   Reg#(Bool) rg5 <- mkReg(True);
   Reg#(Bool) rg6 <- mkReg(True);

   rule set_r5;
     rg5 <= !rg5;
     $display("Changing r5");
   endrule

   rule set_r6;
     rg6 <= !rg6;
     $display("Changing r6");
   endrule

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule
