import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorLFIFO0();
   
   FIFO#(Bit#(32)) f <- myLSizedFIFO(0);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
