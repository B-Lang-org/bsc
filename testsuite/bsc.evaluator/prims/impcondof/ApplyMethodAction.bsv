import FIFO::*;

(* synthesize *)
module sysApplyMethodAction();

   FIFO#(Bool) f1 <- mkFIFO;

   rule r;
      $display("cond = %d", impCondOf(f1.enq(True)));
   endrule

endmodule
