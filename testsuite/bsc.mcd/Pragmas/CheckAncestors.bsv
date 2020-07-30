import Clocks::*;

interface TestIfc;
  // empty
endinterface

(* synthesize
 , clock_ancestors = "c2 AOF c3, default_clock AOF c2"
 *)
module mkTest(Clock c2, Clock c3, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False);

  // This is only legal if c2 is in the same family as the default reset clk
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
module sysCheckAncestors();

  Clock clk1 <- mkAbsoluteClock(5,30);
  Reset rst1 <- mkInitialReset(2, clocked_by clk1);
  ClockDividerIfc div <- mkClockDivider(2, clocked_by clk1, reset_by rst1);

  // This should fail because the default clock is not an ancestor of clk1
  // or div.slowClock
  TestIfc test <- mkTest(div.fastClock, div.slowClock);

endmodule