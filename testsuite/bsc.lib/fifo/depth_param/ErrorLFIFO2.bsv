import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorLFIFO2();
   
   FIFO#(Bit#(32)) f <- myLSizedFIFO(2);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
