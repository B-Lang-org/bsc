import Clocks::*;

// Clock periods
Integer p1 = 6;
Integer p2 = 4;

// This is like OneModuleOutput.bsv but the submodule returns noClock to
// the parent, to test that the simulation compiles and that the rules
// in the parent are not triggered.

(* synthesize *)
module sysNoClock_Output ();
   Clock clk1 <- mkAbsoluteClock(p1, p1);

   SubIFC s <- mkNoClock_Output_Sub();
   Clock clk2 = s.clk;

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

interface SubIFC;
   interface Clock clk;
endinterface

(* synthesize *)
module mkNoClock_Output_Sub (SubIFC);
   interface clk = noClock;
endmodule

