import Clocks::*;

interface TestIfc;
  // empty
endinterface

(* synthesize,
   clock_family = "c2, default_clock"
 *)
module mkTest(Clock c2, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False);

  // This is only legal if c2 is in the same family as the default reset clk
  Reg#(Bool) x2 <- mkReg(True, clocked_by c2);

  // This is only legal if c2 is the same family as the default clock
  rule r;
    x1 <= x2;
    x2 <= x1;
  endrule

endmodule

(* synthesize *)
module sysCheckSameFamily();

  Clock clk <- mkAbsoluteClock(7,23);

  // default clock and clk are not the same family, so this should generate
  // an error.
  TestIfc test <- mkTest(clk);

endmodule