import FIFO::*;
import RegFile::*;

(* synthesize *)
module mkDut();

   Reg#(UInt#(5))              idx <- mkReg(0);
   RegFile#(UInt#(4),Bit#(16)) rf <- mkRegFileFull();
   FIFO#(Bit#(16))             fifo <- mkSizedFIFO(4);
   
   rule incr;
      idx <= idx + 1;
   endrule: incr
   
   rule producer (idx % 2 == 0);
      let n = truncate(idx / 2);
      fifo.enq(rf.sub(n));
   endrule: producer
   
   rule consumer (idx % 4 == 2);
      fifo.deq();
   endrule: consumer
   
endmodule: mkDut