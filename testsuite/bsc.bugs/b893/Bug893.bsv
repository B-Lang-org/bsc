import FIFO::*;
import GetPut::*;

(* synthesize *)
module sysBug893#(Bool r) (Get#(Bool));
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;
   let g1 = fifoToGet(f1);
   let g2 = fifoToGet(f2);

   method get = r ? g1.get : g2.get;
endmodule

	 
