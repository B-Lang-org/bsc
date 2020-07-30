import FIFO::*;
import Vector::*;

(* synthesize *)
module sysAndStaticArraySelectMethodValue();

   Vector#(5, FIFO#(Bool)) fs <- replicateM(mkFIFO);

   let a = fs[0].first && fs[1].first;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
