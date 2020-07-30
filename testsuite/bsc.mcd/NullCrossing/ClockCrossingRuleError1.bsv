import FIFO::*;

(* synthesize *)
module sysClockCrossingRuleError1();

   Reg#(UInt#(4)) x <- mkReg(0);
   FIFO#(UInt#(4)) fifo <- mkFIFO();
   
   // this should fail because it has an implicit condition
   (* clock_crossing_rule *)
   rule incr;
      fifo.enq(x);
      x <= x + 1;
   endrule: incr
   
endmodule: sysClockCrossingRuleError1