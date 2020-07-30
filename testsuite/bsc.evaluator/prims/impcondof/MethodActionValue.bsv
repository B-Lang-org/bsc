import FIFO::*;

interface FIFOPop#(type t);
   method ActionValue#(t) pop();
endinterface

(* synthesize *)
module mkFIFOPop(FIFOPop#(Bool));
   FIFO#(Bool) f <- mkFIFO;

   method ActionValue#(Bool) pop();
      f.deq;
      return f.first;
   endmethod
endmodule

(* synthesize *)
module sysMethodActionValue();

   FIFOPop#(Bool) f1 <- mkFIFOPop;

   rule r;
      $display("cond = %d", impCondOf(f1.pop));
   endrule

endmodule
