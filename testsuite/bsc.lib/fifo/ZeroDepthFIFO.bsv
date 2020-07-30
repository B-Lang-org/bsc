import FIFO::*;

(* synthesize *)
module sysZeroDepthFIFO();
   
  FIFO#(Bit#(32)) f <- mkSizedFIFO(0);

endmodule
   
