import Clocks ::*;

// Clock period
Integer p1 = 5;

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
module sysMakeReset0();

   Clock clk <- mkAbsoluteClock (10, p1);

   MakeResetIfc rst_inst <- mkReset(0, True, clk);
   Reset rst = rst_inst.new_rst;

   Reg#(Bool) c <- mkReg(True, clocked_by clk, reset_by rst);

   // because clk won't start right away, and because we've chosen c
   // to be a synchronous register, we need the reset to hold until
   // the first clock ticks of c
   Reg#(Bit#(8)) rst_count <- mkReg(8);
   rule keep_in_reset (rst_count > 0);
      rst_inst.assertReset;
      rst_count <= rst_count - 1;
   endrule

   rule stop (c);
      $display("Done ", adj_stime(p1));
      $finish(0);
   endrule

endmodule
