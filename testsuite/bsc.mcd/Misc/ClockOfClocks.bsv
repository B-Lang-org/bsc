import Clocks::*;

(* synthesize *)
module sysClockOfClocks(Empty);

Clock c <- exposeCurrentClock();
Reg#(Bool) r <- mkReg(True);

GatedClockIfc g <- mkGatedClockFromCC(True);
Clock c2 = g.new_clk;

Reg#(Bool) s();
mkReg#(True) the_s(s, clocked_by(c2));

Reg#(Bool) t();
mkReg#(True) the_t(t, clocked_by(clockOf(r)));

// we don't care about the answer, but we want to 
// see the warning
rule test;
  // one of these should print 1, not both
  $display(clockOf(s) == clockOf(s && r));
  $display(clockOf(r) == clockOf(s && r));
  $finish(0);
endrule

endmodule
