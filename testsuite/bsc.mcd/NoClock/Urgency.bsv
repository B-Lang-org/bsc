import Clocks::*;

interface ModIfc;
  method Bool isOdd(UInt#(8) value);
  method Bool isEven(UInt#(8) value);
endinterface

import "BVI" Oracle =
module mkOracle(ModIfc);
  default_clock no_clock;
  method ODD_OUT isOdd(ODD_IN);
  method EVEN_OUT isEven(EVEN_IN);
endmodule

(* synthesize *)
module sysUrgency();

  Clock clk2 <- mkAbsoluteClock(7,15);
  Reset rst2 <- mkInitialReset(1, clocked_by clk2);

  Reg#(UInt#(8)) val1 <- mkRegA(19);
  Reg#(UInt#(8)) val2 <- mkRegA(46, clocked_by clk2, reset_by rst2);

  Reg#(Bool) cond1 <- mkRegA(False);
  Reg#(Bool) cond2 <- mkRegA(True, clocked_by clk2, reset_by rst2);

  ModIfc m <- mkOracle;

  rule r1 (cond1);
    if (m.isOdd(val1))
      val1 <= val1 + 3;
    else
      val1 <= val1 - 1;
  endrule

  rule r2 (cond2);
    if (m.isEven(val2))
      val2 <= val2 + 3;
    else
      val2 <= val2 - 1;
  endrule

endmodule