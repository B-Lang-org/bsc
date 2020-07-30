import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorFIFO2();
   
   FIFO#(Bit#(32)) f <- mySizedFIFO(2);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
