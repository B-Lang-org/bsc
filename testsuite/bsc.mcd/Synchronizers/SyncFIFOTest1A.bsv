import Clocks::*;
import FIFO::*;
import StmtFSM::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncFIFOTest1A();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);   
   Reset rst2 <- mkInitialReset(3, clocked_by fast_clk);

   SyncFIFOIfc#(Bit#(8)) sync1 <- mkSyncFIFOFromCC(1, fast_clk);
   Reg#(Bit#(8))  d <- mkReg(0);
   
   Action enq = 
       action
          sync1.enq(d);
          $display ("%t enq %d", $time, d);
          d <= d + 1;
       endaction;
   
   
   let srcSeq =
   (seq
       enq;
       enq;
       delay(200);
       enq;
       delay(100);
    endseq);
   
    Action dq = action sync1.deq; $display ("%t: Took %d", $time, sync1.first); endaction;

   
   let dstSeq =
   (seq
       delay(20);
       dq;
       delay(200);
       dq;
       dq;
       delay(10);
    endseq);
   
   mkAutoFSM(srcSeq);
   mkAutoFSM(dstSeq, clocked_by fast_clk, reset_by rst2);
   
endmodule
