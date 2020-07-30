import Clocks :: *;

// Clock period
Integer p1 = 10;

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
module sysResetEither ();

   Clock clk <- exposeCurrentClock;

   // make two resets (associated with the current clock)
   MakeResetIfc rifc1 <- mkReset(0, False, clk);
   MakeResetIfc rifc2 <- mkReset(0, False, clk);
   Reset rst1 = rifc1.new_rst;
   Reset rst2 = rifc2.new_rst;
   
   // combine the resets
   Reset rst <- mkResetEither(rst1, rst2);

   // state which is reset by the muxed reset
   Reg#(Bit#(32)) val <- mkReg(0, reset_by rst);
   
   Reg#(Bit#(32)) fsm_state <- mkReg(0);

   rule incr_val;
      val <= val + 1;
      $display("(%d) val = %h", adj_stime(p1), val);
   endrule

   rule fsm;
      fsm_state <= fsm_state + 1;
      $display("(%d) executing step %d", adj_stime(p1), fsm_state);

      // The value should be "aa" until we trigger a reset

      // If we trigger a reset of rst1, the value should go to 0
      if (fsm_state == 5)
	 rifc1.assertReset();
      
      // Wait for the value to update
      
      // If we trigger a reset of rst2, the value should go to 0
      if (fsm_state == 8)
	 rifc2.assertReset();

      // Wait for the value to update

      // Trigger rst1 and rst2 together, the value should stay in reset
      // until *both* are deasserted
      if ((fsm_state > 16) && (fsm_state < 20))
	 rifc1.assertReset();
      if ((fsm_state > 15) && (fsm_state < 18))
	 rifc2.assertReset();

      // Wait for the value to update

      if (fsm_state > 22)
	 $finish(0);
   endrule

endmodule
