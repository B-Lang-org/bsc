import Clocks::*;

(* synthesize *)
module sysEUndetClock2(Empty);

  GatedClockIfc g();
  mkGatedClock#(True, ?) the_c_gated(g);
  Clock c = g.new_clk;

  Reg#(Bool) r();
  mkReg#(False) the_r(r, clocked_by c);
 
endmodule


