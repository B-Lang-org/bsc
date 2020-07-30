import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorLFIFO1();
   
   FIFO#(Bit#(32)) f <- myLSizedFIFO(1);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
