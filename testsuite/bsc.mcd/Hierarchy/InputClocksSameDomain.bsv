// Test input clocks in the same domain
// Do the domains of the child get merged properly?  Are rules dumped on
// the resulting single edge?  Etc.

// This compiles as one output module, as a baseline.
// Compile using -g to test that, with synthesis boundaries, Bluesim
// generation does the right thing.

import Clocks::*;

// Clock periods
Integer p1 = 10;

(* synthesize *)
module sysInputClocksSameDomain ();
   Clock c <- exposeCurrentClock;

   // the clocked_by is just add some additional testing for noClock
   mkInputClocksSameDomain_Sub(c,c, clocked_by noClock);
endmodule

module mkInputClocksSameDomain_Sub #(Clock clk1, Clock clk2) ();

   // use RegU to avoid the need for a reset
   Reg#(Bit#(8)) rg1 <- mkRegU(clocked_by clk1);
   Reg#(Bit#(8)) rg2 <- mkRegU(clocked_by clk2);
   
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

   rule r1;
      rg1 <= rg1 + 1;
      $display("(%d) rg1 = %h", adj_stime(p1), rg1);
   endrule
   
   rule r2;
      rg2 <= rg2 + 1;
      $display("(%d) rg2 = %h", adj_stime(p1), rg2);
   endrule

   rule stop (rg1 > (init_val + 17));
      $finish(0);
   endrule

endmodule


