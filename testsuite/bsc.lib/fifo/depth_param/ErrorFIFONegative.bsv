import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorFIFONegative();
   
   FIFO#(Bit#(32)) f <- mySizedFIFO(-1);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
