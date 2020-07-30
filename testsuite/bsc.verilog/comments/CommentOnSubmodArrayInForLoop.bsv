import FIFO::*;

(* synthesize *)
module mkCommentOnSubmodArrayInForLoop();

   FIFO#(Bool) fs[4];
   for (Integer i=0; i<4; i=i+1)
      (* doc = "This is also a FIFO" *)
      fs[i] <- mkFIFO;

endmodule

