import FIFO::*;
import Vector::*;

(* synthesize *)
module sysAndMethodValue();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   let a = f1.first && f2.first;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
