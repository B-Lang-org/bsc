import Clocks::*;

(* synthesize *)
module sysEClockMux2(Clock c1, Clock c2, Empty ifc);
  Reg#(Bool) b <- mkReg(False);
 
  // illegally muxed clock
  Clock c = b ? c1 : c2;
  
  GatedClockIfc g();
  mkGatedClock#(True, c) the_g(g);
  Clock c_gated = g.new_clk;

  Reg#(Bit#(32)) x();
  mkRegU the_x(x, clocked_by c_gated);  
endmodule
