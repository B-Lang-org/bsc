// This tests the time-0 behavior by checking that the inverted clock
// has a posedge at time-0 corresponding to the absolute clock starting
// with value 0 (and remaining that way through the delay).

import Clocks::*;

// Clock period
Integer p1 = 10;

// the initial value of the registers will be AA
Bit#(8) init_val = 8'hAA;

// function to make $stime the same for Bluesim and Verilog
function ActionValue#(Bit#(32)) adj_stime(Integer p);
   actionvalue
      let adj = (p + 1) / 2;
      let t <- $stime();
      if (genVerilog)
	 return (t + fromInteger(adj));
      else
	 return t;
   endactionvalue
endfunction

(* synthesize *)
module sysInvertAbsoluteClock();
   Clock clk1 <- mkAbsoluteClock(15, p1);

   ClockDividerIfc i <- mkClockInverter (clocked_by clk1);
   Clock clk2 = i.slowClock;

   Reg#(Bit#(8)) rg <- mkRegU(clocked_by clk2);

   rule tick;
      $display("(%d) rg = %h", adj_stime(p1), rg);
      rg <= rg + 1;
      if (rg == init_val + 4)
	 $finish(0);
   endrule
endmodule

