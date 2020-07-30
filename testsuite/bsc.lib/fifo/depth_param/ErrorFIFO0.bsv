import FIFO::*;
import FIFOParam::*;

(* synthesize *)
module sysErrorFIFO0();
   
   FIFO#(Bit#(32)) f <- mySizedFIFO(0);
   
   rule test;
      f.enq(0);
      $finish(0);
   endrule
   
endmodule
  
   
