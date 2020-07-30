import Clocks::*;

interface TestIfc;
  // empty
endinterface

(* synthesize
 , clock_ancestors = "default_clock AOF c2 AOF c3"
 , gate_all_clocks
 *)
module mkTest(Clock c2, Clock c3, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False);

  // This is only legal if c2 is in the same family as the default reset
  Reg#(Bool) x2 <- mkReg(True, clocked_by c2);

  Reg#(Bool) x3 <- mkReg(False, clocked_by c3, reset_by noReset);

  // This is only legal if c2 and c3 are the same family as the default clock
  rule r;
    x1 <= x2;
    x2 <= x1;
    x3 <= x1 != x2;
  endrule

endmodule

(* synthesize *)
module sysAncestorsBoundary();

  Clock clk <- exposeCurrentClock;
 
  GatedClockIfc gc1 <- mkGatedClock(True, clk);
  Clock clk1 = gc1.new_clk;

  GatedClockIfc gc2 <- mkGatedClock(False, clk1);
  Clock clk2 = gc2.new_clk;

  // This is OK because the default clock, clk1 and clk2 are in the same family
  TestIfc test <- mkTest(clk1, clk2);

endmodule