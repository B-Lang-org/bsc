import Clocks::*;

// Clock periods
Integer p1 = 6;
Integer p2 = 4;

// This is like OneModule.bsv but it tests the handling of input and
// output clocks by passing the two clocks into the module (which is
// a submod here but was the topmod in OneModule.bsv) where one of the
// passed clocks is noClock.  This tests that the simulation compiles
// and that the rules in the submod are not triggered.

(* synthesize *)
module sysNoClock_Input ();
   Clock clk1 <- mkAbsoluteClock(p1, p1);
   Clock clk2 = noClock;

   // the clocked_by is just for the heck of it, since that clock is unused.
   // clk2 is the real test
   mkNoClock_Input_Sub(clk1, clk2, clocked_by noClock);
endmodule

(* synthesize *)
module mkNoClock_Input_Sub#(Clock clk1, Clock clk2) ();
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
      $display("(%d) rg2 = %h", adj_stime(p2), rg2);
   endrule

   rule stop (rg1 > (init_val + 17));
      $finish(0);
   endrule

endmodule

