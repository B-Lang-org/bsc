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
module sysActionMethodActionValue();

   FIFOPop#(Bool) f1 <- mkFIFOPop;
   FIFOPop#(Bool) f2 <- mkFIFOPop;

   Action a =
      action
         Bool b1 <- f1.pop;
         Bool b2 <- f2.pop;
	 $display(b1, b2);
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
