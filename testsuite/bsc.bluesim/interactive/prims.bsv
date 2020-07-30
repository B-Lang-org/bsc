import FIFO::*;
import RegFile::*;
import Probe::*;

(* synthesize *)
module mkPrims();
   
   Reg#(UInt#(16)) count <- mkReg(0);
   FIFO#(UInt#(16)) fifo <- mkFIFO();
   RegFile#(UInt#(8),UInt#(16)) rf <- mkRegFileFull();
   Probe#(UInt#(16)) probe <- mkProbe();
   Wire#(UInt#(16)) w <- mkWire();
   
   rule incr (count < 100);
      count <= count + 1;
   endrule: incr
   
   rule do_stuff;
      let addr = truncate(count);
      rf.upd(addr,count);
      w <= count;
   endrule: do_stuff
   
   rule do_more_stuff;
      fifo.enq(w);      
   endrule: do_more_stuff
   
   rule drain;
      probe <= fifo.first();
      fifo.deq();
   endrule: drain
   
   rule done (count == 1000);
      $finish(0);
   endrule: done

endmodule
