import Clocks::*;

typedef UInt#(8) T;

// make a submodule which requires an ungated clock
(* synthesize *)
module mkTestMkUngatedClock_Sub(ReadOnly#(T));
   Reg#(T) cntr2 <- mkReg(0);

   rule incr;
      $display("%t: cntr2 = %d", $time, cntr2);
      cntr2 <= cntr2 + 1;
   endrule

   method _read = cntr2;
endmodule

(* synthesize *)
module sysTestMkUngatedClock();

  Reg#(UInt#(3)) cntr <- mkReg(0);

  // make an ungated clock
  MakeClockIfc#(Bool) mc <- mkUngatedClock(False);
  Clock clk2 = mc.new_clk;

  Reset rst2 <- mkAsyncResetFromCR(2, clk2);

  // if clk2 has a gate, this instantiation will fail
  ReadOnly#(T) s <- mkTestMkUngatedClock_Sub(clocked_by clk2,
					     reset_by rst2);

  // generate the clk2 shape based on cntr: /1\2/2\3
  rule shape_clk2;
    mc.setClockValue(cntr == 0 || cntr == 3 || cntr == 4);
    cntr <= cntr + 1;
  endrule

  rule done (s == 100);
    $finish(0);
  endrule

endmodule
