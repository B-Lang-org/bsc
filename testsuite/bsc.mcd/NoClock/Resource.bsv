import Clocks::*;

interface ModIfc;
  method Bool isOdd(UInt#(8) value);
endinterface

import "BVI" Oracle =
module mkOracle(ModIfc);
  method OUT isOdd(IN) clocked_by(no_clock);
  schedule isOdd CF isOdd;
endmodule

(* synthesize *)
module sysResource();

  Clock clk2 <- mkAbsoluteClock(7,15);
  Reset rst2 <- mkInitialReset(1, clocked_by clk2);

  Reg#(UInt#(8)) val1 <- mkRegA(19);
  Reg#(UInt#(8)) val2 <- mkRegA(46, clocked_by clk2, reset_by rst2);

  Reg#(Bool) cond1 <- mkRegA(False, clocked_by noClock);
  Reg#(Bool) cond2 <- mkRegA(True, clocked_by noClock, reset_by rst2);

  ModIfc m <- mkOracle;

  rule r1 (cond1);
    $display(m.isOdd(val1));
  endrule

  rule r2 (!cond2);
    $display(m.isOdd(val2));
  endrule

endmodule