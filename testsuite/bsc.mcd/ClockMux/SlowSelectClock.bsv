import Clocks::*;

(* synthesize *)
module sysSlowSelectClock(Empty);

  // the start time of 12 and clock period of 4 allows for output edges
  // during the select cycle as well as a rising edge coincident with
  // the end of the select cycle (to test that that edge is also ignored)
  Clock clk4 <- mkAbsoluteClock(12, 4);
  Clock clk6 <- mkAbsoluteClock(12, 6);

  SelectClkIfc cs <- mkClockSelect(1, clk4, clk6);
  Clock clkM = cs.clock_out;
  Reset rstM = cs.reset_out;

  Reg#(Bit#(14)) real_counter <- mkReg(0, clocked_by clkM, reset_by rstM);

  Reg#(Bool) selected <- mkReg(False);

  rule select (!selected);
     cs.select(True);
     selected <= True;
     $display ("Clock Select A");
  endrule

  rule test;
     real_counter <= real_counter + 1;
     $display("Real counter: %0d Time %t", real_counter, $time);
     if (real_counter == 9)
	$finish(0);
  endrule

endmodule



