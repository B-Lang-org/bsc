import FIFO::*;

(* synthesize *)
module sysActionMethodAction();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Action a =
      action
         f1.deq;
         f2.deq;
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
