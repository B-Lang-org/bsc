import Clocks::*;
import FIFO::*;

Integer period_slow_clk2 = 509;
Integer period_slow_clk1 = 109;
Integer period_base_clk  = 101;
Integer period_fast_clk1 = 97;
Integer period_fast_clk2 = 23;

typedef UInt#(16) DataT;

UInt#(32)  finishAt = 50000;

(* synthesize *)
module sysSyncRegTest3();

   Clock slow_clk2 <- mkAbsoluteClock(3, period_slow_clk2);
   Clock slow_clk1 <- mkAbsoluteClock(4, period_slow_clk1);
   Clock base_clk  <- mkAbsoluteClock(5, period_base_clk);
   Clock fast_clk1 <- mkAbsoluteClock(6, period_fast_clk1);
   Clock fast_clk2 <- mkAbsoluteClock(7, period_fast_clk2);

   Reset slow_rst2 <- mkAsyncResetFromCR( 2, slow_clk2);
   Reset slow_rst1 <- mkAsyncResetFromCR( 2, slow_clk1);
   Reset base_rst  <- mkAsyncResetFromCR( 2, base_clk);
   Reset fast_rst1 <- mkAsyncResetFromCR( 2, fast_clk1);
   Reset fast_rst2 <- mkAsyncResetFromCR( 2, fast_clk2);

   DutIfc fastToSlow2 <- mkTestSync( slow_clk2, slow_rst2, clocked_by base_clk, reset_by base_rst);
   DutIfc fastToSlow1 <- mkTestSync( slow_clk1, slow_rst1, clocked_by base_clk, reset_by base_rst);
   DutIfc slowToFast1 <- mkTestSync( fast_clk1, fast_rst1, clocked_by base_clk, reset_by base_rst);
   DutIfc slowToFast2 <- mkTestSync( fast_clk2, fast_rst2, clocked_by base_clk, reset_by base_rst);

   Reg#(UInt#(32)) tick <- mkRegA(0, clocked_by base_clk, reset_by base_rst);

   rule stop (True);
      tick <= tick + 1;
      if (tick == finishAt) begin
         $finish(0);
      end
   endrule
   rule report4 (tick == finishAt - 4);
      fastToSlow2.report();
   endrule
   rule report3 (tick == finishAt - 3);
      fastToSlow1.report();
   endrule
   rule report2 (tick == finishAt - 2);
      slowToFast1.report();
   endrule
   rule report1 (tick == finishAt - 1);
      slowToFast1.report();
   endrule
endmodule

interface DutIfc ;
   method Action report;
endinterface

(*synthesize*)
module mkTestSync #(Clock dstclk, Reset dstrst ) (DutIfc);

   Reg#(Bool)  run <- mkReg(True);

   Reg#(DataT) sync1 <- mkSyncRegFromCC(0, dstclk);

   Reg#(DataT) sendS <- mkReg(0);
   Reg#(DataT) recvD <- mkReg(0, clocked_by dstclk, reset_by dstrst);

   rule s_send (run);
      sync1 <= sendS+1;
      sendS <= sendS + 1;
      //$display ("Sending %m:  %d", sendS+1);
   endrule

   rule d_recv (recvD != sync1);
      if ((recvD + 1) != sync1) begin
         $display ("ERROR: %m missing data -- expected %d, got %d", recvD+1, sync1);
      end
      else begin
         //$display ("Received %m:  %d", sync1);
      end
      recvD <= sync1;
   endrule
   
   method Action report ();
      $display ("%m reports %d sends", sendS);
   endmethod

endmodule
