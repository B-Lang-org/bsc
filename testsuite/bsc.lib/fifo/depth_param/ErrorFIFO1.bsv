import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorFIFO1();
   
   FIFO#(Bit#(32)) f <- mySizedFIFO(1);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
