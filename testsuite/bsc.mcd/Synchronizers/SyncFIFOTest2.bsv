import Clocks::*;
import FIFO::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncFIFOTest2();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);   

   Reset rst2 <- mkInitialReset(3, clocked_by fast_clk);

   SyncFIFOIfc#(Bit#(8)) sync1 <- mkSyncFIFOFromCC(4, fast_clk);
   SyncFIFOIfc#(Bit#(8)) sync2 <- mkSyncFIFOToCC(4, fast_clk, rst2);

   // use RegU to avoid the need for a reset
   Reg#(Bit#(8)) last     <- mkRegU;
   Reg#(Bit#(8)) sent     <- mkRegU(clocked_by fast_clk);
   Reg#(Bit#(8)) received <- mkRegU(clocked_by fast_clk);

   (* descending_urgency="start, send_val" *)
   (* descending_urgency="start, get_val" *)

   // the initial value of the registers will be AAAA...AAAA
   rule start (last == 8'hAA);
      last <= 0;
   endrule

   (* descending_urgency="start2, reflect_val" *)

   rule start2 (sent == 8'hAA);
      sent <= 0;
      received <= 0;
   endrule

   rule send_val (last != 8'hAA);
      $display("%t: Sent val %d", $time, last + 1);
      sync1.enq(last + 1);
   endrule

   rule receive_val;
     if (sync1.first() > received)
     begin
       $display("%t: Recorded val %d", $time, sync1.first());
       received <= sync1.first();
     end
     sync1.deq();
   endrule

   rule reflect_val (received > sent);
     $display("%t: Reflected val %d", $time, sent + 1);
     sync2.enq(sent + 1);
     sent  <= sent + 1;
   endrule

   rule get_val;
     if (sync2.first() != last)
     begin
       $display("%t: Got value %d", $time, sync2.first());
       last <= sync2.first();
     end
     sync2.deq();
   endrule
   
   rule show_empty_full_1;
     $display ("sync1.notFull  = %b", sync1.notFull());
     $display ("sync2.notEmpty = %b", sync2.notEmpty());
   endrule
   
   rule show_empty_full_2;
     $display ("sync1.notEmpty = %b", sync1.notEmpty());
     $display ("sync2.notFull  = %b", sync2.notFull());
   endrule
   
   rule stop (last == 40);
      $finish(0);
   endrule

endmodule
