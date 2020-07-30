import Clocks::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncPulseTest();

   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);   
   SyncPulseIfc sync1 <- mkSyncPulseFromCC(fast_clk);
   SyncPulseIfc sync2 <- mkSyncPulseToCC(fast_clk, noReset());

   // use RegU to avoid the need for a reset
   Reg#(Bool)    waiting <- mkRegU;
   Reg#(Bit#(8)) count <- mkRegU;

   (* descending_urgency="start, do_pulse" *)
   (* descending_urgency="start, get_pulse" *)

   // the initial value of the registers will be AAAA...AAAA
   rule start (count == 8'hAA);
      count <= 0;
      waiting <= False;
   endrule

   rule do_pulse (count != 8'hAA && !waiting);
      $display("Sent pulse");
      sync1.send();
      waiting <= True;
   endrule

   rule reflect (sync1.pulse());
     $display("Reflected pulse");
     sync2.send();
   endrule

   rule get_pulse(sync2.pulse());
     $display("Got reflected pulse");
     count <= count + 1;
     waiting <= False;
   endrule

   rule stop (count == 40);
      $finish(0);
   endrule

endmodule
