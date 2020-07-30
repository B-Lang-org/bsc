import Clocks::*;
import FIFO::*;

Integer period_slow_clk2 = 509;
Integer period_slow_clk1 = 109;
Integer period_base_clk  = 101;
Integer period_fast_clk1 = 97;
Integer period_fast_clk2 = 23;

typedef UInt#(16) DataT;

(* synthesize *)
module sysSyncHandshakeTest2();

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

   DutIfc fastToSlow2 <- mkTestSyncHS( slow_clk2, slow_rst2, clocked_by base_clk, reset_by base_rst);
   DutIfc fastToSlow1 <- mkTestSyncHS( slow_clk1, slow_rst1, clocked_by base_clk, reset_by base_rst);
   DutIfc slowToFast1 <- mkTestSyncHS( fast_clk1, fast_rst1, clocked_by base_clk, reset_by base_rst);
   DutIfc slowToFast2 <- mkTestSyncHS( fast_clk2, fast_rst2, clocked_by base_clk, reset_by base_rst);

   Reg#(UInt#(32)) tick <- mkRegA(0, clocked_by base_clk, reset_by base_rst);
   
   
   UInt#(32) endTest = 50000 ; 
   rule stop (True);
      tick <= tick + 1;
      if (tick == endTest) begin
         $finish(0);
      end
   endrule

   rule stoptest  (tick == endTest - 100);
      fastToSlow2.stop;
      fastToSlow1.stop;
      slowToFast1.stop;
      slowToFast2.stop;
   endrule
   rule compare5 (tick == endTest - 5);
      fastToSlow2.compare;
   endrule
   rule compare4 (tick == endTest - 4);
      fastToSlow1.compare;
   endrule
   rule compare3 (tick == endTest - 3);
      slowToFast1.compare;
   endrule
   rule compare2 (tick == endTest - 2);
      slowToFast2.compare;
   endrule

endmodule

interface DutIfc ;
   method Action compare;
   method Action stop;
endinterface

(*synthesize*)
module mkTestSyncHS #(Clock dstclk, Reset dstrst ) (DutIfc);

   Clock srcClk <- exposeCurrentClock;
   Reg#(Bool)  run <- mkReg(True);

   SyncPulseIfc sync1 <- mkSyncHandshakeFromCC(dstclk);

   Reg#(DataT) sendCount <- mkReg(0);
   CrossingReg#(DataT) recvCount <- mkNullCrossingRegA(srcClk, 0, clocked_by dstclk, reset_by dstrst);

   rule s_send (run);
      sync1.send;
      sendCount <= sendCount + 1;
      //$display ("Sending %m:  %d", sendS+1);
   endrule

   rule d_recv (sync1.pulse);
      recvCount <= recvCount + 1;
   endrule

   method Action compare ;
      if (recvCount.crossed != sendCount) begin
         $display ( "Error: %m send and receive counts differ %d vs %d", sendCount, recvCount.crossed );
      end
      else begin
         $display (  "OK: %m send and receive counts are Equal %d vs %d", sendCount, recvCount.crossed );
      end
   endmethod

   method Action stop = run._write(False);

endmodule
