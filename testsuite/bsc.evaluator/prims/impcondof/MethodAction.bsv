import FIFO::*;

(* synthesize *)
module sysMethodAction();

   FIFO#(Bool) f1 <- mkFIFO;

   rule r;
      $display("cond = %d", impCondOf(f1.enq));
   endrule

endmodule
