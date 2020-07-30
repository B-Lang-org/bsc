import Clocks::*;

interface ModIfc;
  method Bool isOdd(UInt#(8) value);
endinterface

import "BVI" Oracle =
module mkOracle(ModIfc);
  method OUT isOdd(IN) clocked_by(no_clock);
endmodule

(* synthesize *)
module sysUnclockedCond();

  Clock clk2 <- mkAbsoluteClock(7,15);
  Reset rst2 <- mkInitialReset(1, clocked_by clk2);

  Reg#(UInt#(8)) val1 <- mkRegA(19);
  Reg#(UInt#(8)) val2 <- mkRegA(46, clocked_by clk2, reset_by rst2);

  Reg#(Bool) cond <- mkRegA(False, clocked_by noClock);

  ModIfc m <- mkOracle;

  rule r1 (cond);
    $display(m.isOdd(val1));
  endrule

  rule r2 (!cond);
    $display(m.isOdd(val2));
  endrule

endmodule
