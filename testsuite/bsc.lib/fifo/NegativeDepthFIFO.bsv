import FIFO::*;

(* synthesize *)
module sysNegativeDepthFIFO();
   
   FIFO#(Bit#(32)) f <- mkSizedFIFO(-1);
  
endmodule
 
