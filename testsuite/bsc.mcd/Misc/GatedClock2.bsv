import Clocks::*;

(* synthesize *)
module sysGatedClock2(Empty);

Clock c <- exposeCurrentClock();

GatedClockIfc g <- mkGatedClock(True, c);
Clock c2 = g.new_clk;

Reg#(Bool) s();
mkReg#(sameFamily(c,c2)) the_s(s, clocked_by(c2));

rule go;
  s <= !s;
  g.setGateCond(False);
endrule

endmodule
