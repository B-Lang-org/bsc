import Clocks::*;

(* synthesize *)
module sysClockOf(Empty);

Clock c <- exposeCurrentClock();
Reg#(Bool) r <- mkReg(True);

GatedClockIfc g <- mkGatedClockFromCC(True);
Clock c2 = g.new_clk;

Reg#(Bool) s();
mkReg#(True) the_s(s, clocked_by(c2));

Reg#(Bool) t();
mkReg#(True) the_t(t, clocked_by(clockOf(r)));

rule test;
  if((clockOf(s) != (clockOf(r))) && (clockOf(r) == clockOf(t)) &&
     (clockOf(0) == noClock)) 
     $display("PASS");
  else
     $display("FAIL");
  $finish(0);
endrule

endmodule
