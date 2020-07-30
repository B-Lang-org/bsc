import Clocks::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncHandshakeTest();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);   
   SyncPulseIfc sync1 <- mkSyncHandshakeFromCC(fast_clk, reset_by noReset);
   SyncPulseIfc sync2 <- mkSyncHandshakeToCC(fast_clk, noReset);

   // use RegU to avoid the need for a reset
   Reg#(Bit#(8)) count <- mkRegU;
   Reg#(Bit#(8)) pending <- mkRegU(clocked_by fast_clk);
   PulseWire reflected <- mkPulseWire(clocked_by fast_clk, reset_by noReset);

   (* descending_urgency="start, do_pulse" *)
   (* descending_urgency="start, get_pulse" *)

   // the initial value of the registers will be AAAA...AAAA
   rule start (count == 8'hAA);
      count <= 0;
   endrule

   (* descending_urgency = "start2, store, unstore" *)

   rule start2 (pending == 8'hAA);
      pending <= 0;
   endrule

   rule do_pulse (count != 8'hAA);
      $display("Sent pulse");
      sync1.send();
   endrule

   (* descending_urgency = "reflect, store, unstore" *)
   rule reflect (sync1.pulse());
     $display("Reflected pulse");
     sync2.send();
     reflected.send();
   endrule

   rule store (sync1.pulse() && !reflected);
     $display("Stored pulse");
     pending <= pending + 1;
   endrule

   rule unstore (pending > 0);
     $display("Reflected stored pulse");
     sync2.send();
     pending <= pending - 1;
   endrule
     
   rule get_pulse(sync2.pulse());
     $display("Got reflected pulse");
     count <= count + 1;
   endrule

   rule stop (count == 40);
      $finish(0);
   endrule

endmodule
