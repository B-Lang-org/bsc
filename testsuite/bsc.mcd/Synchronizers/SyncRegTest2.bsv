import Clocks::*;
import FIFO::*;

Integer period_cc = 10;
Integer period_fast_clk = 4266;
Integer period_slow_clk = 10240;

(* synthesize *)
module sysSyncRegTest2();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);
   Clock slow_clk <- mkAbsoluteClock(2, period_slow_clk);

   Reset fast_rst <- mkAsyncResetFromCR( 2, fast_clk);
   Reset slow_rst <- mkAsyncResetFromCR( 2, slow_clk);

   Empty fastToSlow <- mkTestSync( slow_clk, slow_rst, clocked_by fast_clk, reset_by fast_rst);
   Empty slowToFast <- mkTestSync( fast_clk, fast_rst, clocked_by slow_clk, reset_by slow_rst);

   Reg#(UInt#(32)) tick <- mkReg(0);

   rule stop (True);
      tick <= tick + 1;
      if (tick > 50000) $finish(0);
   endrule

endmodule


(*synthesize*)
module mkTestSync #(Clock dstclk, Reset dstrst ) (Empty);

   Reg#(Bit#(8)) sync1 <- mkSyncRegFromCC(0, dstclk);

   Reg#(Bit#(8)) sendS <- mkReg(0);
   Reg#(Bit#(8)) recvD <- mkReg(0, clocked_by dstclk, reset_by dstrst);

   rule s_send (True);
      sync1 <= sendS+1;
      sendS <= sendS + 1;
      $display ("Sending %m:  %d", sendS+1);
   endrule

   rule d_recv (recvD != sync1);
      if ((recvD + 1) != sync1) begin
         $display ("ERROR: %m missing data -- expected %d, got %d", recvD+1, sync1);
      end
      else begin
         $display ("Received %m:  %d", sync1);
      end
      recvD <= sync1;
   endrule


endmodule
