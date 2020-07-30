import FIFO::*;
import List::*;

interface MethodCond3#(type a);
   method Action send(a d, Bit#(1) i);
endinterface

(* synthesize *)
module mkMethodCond3_32(MethodCond3#(Bit#(32)));

   List#(FIFO#(Bit#(32))) ff <- replicateM(2, mkFIFO);
   
   method Action send(d,i);
      (ff[i]).enq(d);
   endmethod
   
endmodule
