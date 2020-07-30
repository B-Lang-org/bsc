import Clocks::*;
import FIFO::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncRegTest();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);   
   Reg#(Bit#(8)) sync1 <- mkSyncRegFromCC(0, fast_clk);
   Reg#(Bit#(8)) sync2 <- mkSyncRegToCC(0, fast_clk, noReset());

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
      $display("Sent val %d", last + 1);
      sync1 <= last + 1;
   endrule

   rule receive_val (sync1 > received);
     $display("Recorded val %d", sync1);
     received <= sync1;
   endrule

   rule reflect_val (received > sent);
     $display("Reflected val %d", sent + 1);
     sync2 <= sent + 1;
     sent  <= sent + 1;
   endrule

   rule get_val (sync2 != 8'hAA && sync2 != last);
     $display("Got value %d", sync2);
     last <= sync2;
   endrule

   rule stop (last == 40);
      $finish(0);
   endrule

endmodule
