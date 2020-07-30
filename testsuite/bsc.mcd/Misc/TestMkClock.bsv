import Clocks::*;

typedef UInt#(8) T;

// make a submodule with a gated clock
(* synthesize *)
(* gate_all_clocks *)
module mkTestMkClock_Sub(ReadOnly#(T));
   Reg#(T) cntr2 <- mkReg(0);

   rule incr;
      $display("%t: cntr2 = %d", $time, cntr2);
      cntr2 <= cntr2 + 1;
   endrule

   method _read = cntr2;
endmodule

(* synthesize *)
module sysTestMkClock();

  Reg#(UInt#(3)) cntr <- mkReg(0);

  MakeClockIfc#(Bool) mc <- mkClock(False, True);
  Clock clk2 = mc.new_clk;

  Reset rst2 <- mkAsyncResetFromCR(2, clk2);

  ReadOnly#(T) s <- mkTestMkClock_Sub(clocked_by clk2,
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
