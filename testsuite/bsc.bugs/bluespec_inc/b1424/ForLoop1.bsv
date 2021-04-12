// We expect the rules to schedule in the order
// they are elaborated (set_r, set_r_1, set_r_2, done).

import Clocks::*;

(* synthesize *)
module sysForLoop1();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   Reg#(Bool) rgs[3] = {rg1, rg2, rg3};

   for (Integer i=0; i<3; i=i+1)
     rule set_r;
       rgs[i] <= !rgs[i];
       $display("Changing r%0d", (i+1));
     endrule

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule
