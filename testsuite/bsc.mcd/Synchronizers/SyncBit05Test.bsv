import Clocks::*;

Integer period_cc = 10;
Integer period_fast_clk = 7;

(* synthesize *)
module sysSyncBit05Test();
   Clock fast_clk <- mkAbsoluteClock(2, period_fast_clk);
   SyncBitIfc#(Bit#(1)) sync1 <- mkSyncBit05FromCC(fast_clk);
   SyncBitIfc#(Bit#(1)) sync2 <- mkSyncBit05ToCC(fast_clk, noReset());

   // use RegU to avoid the need for a reset
   Reg#(Bit#(1)) flipper <- mkRegU;
   Reg#(Bit#(1)) flipper2 <- mkRegU;
   Reg#(Bit#(8)) count <- mkRegU;

   (* descending_urgency="start, flip" *)

   // the initial value of the registers will be AAAA...AAAA
   rule start (count == 8'hAA);
      count <= 0;
      sync1.send(flipper);
   endrule

   // We have to register the result to prevent a race condition
   // when the $display is moved to the negedge in Verilog!
   rule read_sync2;
     flipper2 <= sync2.read();
   endrule

   rule flip (flipper2 == flipper);
      $display("flip!");
      flipper <= ~flipper;
      count <= count + 1;
      sync1.send(~flipper);
   endrule

   rule bridge;
      sync2.send(sync1.read());
   endrule

   rule stop (count == 40);
      $finish(0);
   endrule

endmodule
