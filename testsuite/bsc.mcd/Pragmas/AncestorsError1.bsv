import Clocks::*;

interface TestIfc;
  // empty
endinterface

// This is an error because there is only one clock supplied for c3
(* synthesize
 , clock_ancestors = "default_clock AOF c2, c3"
 *)
module mkTest(Clock c2, Clock c3, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False);

  // This is only legal if c2 is in the same family as the default reset clk
  Reg#(Bool) x2 <- mkReg(True, clocked_by c2);

  // This is only legal if c3 is in the same family as the default reset clk
  Reg#(Bool) x3 <- mkReg(False, clocked_by c3);

  // This is only legal if c2 and c3 are the same family as the default clock
  rule r;
    x1 <= x2;
    x2 <= x1;
    x3 <= x1 != x2;
  endrule

endmodule

(* synthesize *)
module sysAncestorsError1();

  ClockDividerIfc div <- mkClockDivider(2);

  // This is an error because the clocks are not in the same family,
  // but the error in the pragma should be reported first.
  TestIfc test <- mkTest(div.fastClock, div.slowClock);

endmodule