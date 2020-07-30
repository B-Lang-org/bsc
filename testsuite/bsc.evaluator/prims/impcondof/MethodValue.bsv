import FIFO::*;

(* synthesize *)
module sysMethodValue();

   FIFO#(Bool) f1 <- mkFIFO;

   rule r;
      $display("cond = %d", impCondOf(f1.first));
   endrule

endmodule
