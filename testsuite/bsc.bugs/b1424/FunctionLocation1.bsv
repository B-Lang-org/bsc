// We expect the rules to schedule in the order
// they are elaborated (set_r3, set_r2, set_r1, done).

import Clocks::*;

function Rules mkRules(Reg#(Bool) r1, Reg#(Bool) r2);
  return (rules
            rule set_r2;
              r2 <= !r2;
              $display("Changing r2");
            endrule
            rule set_r1;
              r1 <= !r1;
              $display("Changing r1");
            endrule
          endrules);
endfunction

(* synthesize *)
module sysFunctionLocation1();
   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True);
   Reg#(Bool) rg3 <- mkReg(True);

   rule set_r3;
     rg3 <= !rg3;
     $display("Changing r3");
   endrule

   addRules(mkRules(rg1,rg2));

   ReadOnly#(Bool) in_reset <- isResetAssertedDirect();

   rule done if (!in_reset);
      $display("Exiting...");
      $finish(0);
   endrule

endmodule
