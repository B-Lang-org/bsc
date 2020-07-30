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
module sysResetMux ();

   Clock clk <- exposeCurrentClock;

   // make two resets (associated with the current clock)
   MakeResetIfc rifc1 <- mkReset(0, False, clk);
   MakeResetIfc rifc2 <- mkReset(0, False, clk);
   Reset rst1 = rifc1.new_rst;
   Reset rst2 = rifc2.new_rst;
   
   // mux the resets
   MuxRstIfc rmux <- mkResetMux(rst1, rst2);
   Reset rst = rmux.reset_out;

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

      // The selector should start with rst2, but let's select that again,
      // which also tests that the edge should not trigger again
      if (fsm_state == 3)
	 rmux.select(False);

      // If we trigger a reset of rst1, the mux output should not change
      if (fsm_state == 5)
	 rifc1.assertReset();

      // If we trigger a reset, the value should go to 0
      if (fsm_state == 7)
	 rifc2.assertReset();

      // Select the other reset, and change the counter value
      if (fsm_state == 9) begin
	 rmux.select(True);
      end

      // Check that rst2 does nothing
      if (fsm_state == 11)
	 rifc2.assertReset();

      // And rst1 resets the state
      if (fsm_state == 13)
	 rifc1.assertReset();

      // Wait for the value to update

      // Trigger rst2
      if (fsm_state == 16)
	 rifc2.assertReset();

      // And select rst2 again
      // (is this a race condition? or no reset?)
      if (fsm_state == 17)
	 rmux.select(False);

      // Wait for the value to update

      // Assert rst1 and keep it reset, while selecting rst1
      if (fsm_state == 19)
	 rifc1.assertReset();
      if (fsm_state == 20) begin
	 rifc1.assertReset();
	 rmux.select(True);
      end

      if (fsm_state > 22)
	 $finish(0);
   endrule

endmodule
