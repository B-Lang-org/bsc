import FIFO::*;

(* synthesize *)
module sysSchedCondsSimple();
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Reg#(Bool) c <- mkRegU;

   rule r1;
      if (c)
         f1.enq(True);
      else
         f2.enq(True);
   endrule

   rule r2;
      if (c)
         f2.enq(False);
      else
         f1.enq(False);
   endrule
endmodule

