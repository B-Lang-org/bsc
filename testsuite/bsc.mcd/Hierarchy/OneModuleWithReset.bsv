import Clocks::*;

// Clock periods
Integer p1 = 3;
Integer p2 = 2;

(* synthesize *)
module sysOneModuleWithReset ();
   Clock clk1 <- mkAbsoluteClock(p1, p1);
   Reset rst1 <- mkAsyncResetFromCR (2, clk1);

   Clock clk2 <- mkAbsoluteClock(p2, p2);
   Reset rst2 <- mkAsyncResetFromCR (2, clk2);
   
   Reg#(Bit#(8)) rg1 <- mkReg(0, clocked_by clk1, reset_by rst1);
   Reg#(Bit#(8)) rg2 <- mkReg(0, clocked_by clk2, reset_by rst2);

   // function
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

   rule stop (rg1 > 17);
      $finish(0);
   endrule

endmodule

