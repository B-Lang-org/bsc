import FIFO::*;

(* synthesize *)
module sysTest();

   // ---------------

   Reg#(int) rg1 <- mkReg(0);
   Reg#(int) rg2 <- mkRegU;

   // while both r1 and r2 read rg2, it should not count as a shared method
   rule r1;
      rg1 <= rg1 + rg2;
   endrule

   rule r2;
      rg1 <= 17 + rg2;
   endrule

   // ---------------
   // test with an execution order attribute

   Reg#(int) rg3 <- mkReg(0);

   (* execution_order="r3,r4" *)
   rule r3;
      rg3 <= 0;
   endrule

   rule r4;
      rg3 <= 1;
   endrule

   // ---------------
   // Two uses of clear should not count, because it has no arguments

   FIFO#(Bool) fifo <- mkFIFO;
   Reg#(Bool) rg4 <- mkRegU;
   Reg#(Bool) rg5 <- mkRegU;

   rule r5;
      fifo.clear;
      rg4 <= True;
   endrule

   rule r6;
      fifo.clear;
      rg5 <= False;
   endrule

endmodule

