import GetPut::*;
import FIFO::*;

// The "loopy" FIFO allows an enq to a
// full FIFO as long as there is a deq in the same
// cycle.

// This means that the display_output rule that
// calls deq should be more urgent than the put
// method which calls enq.

(* synthesize *)
module mkPutTest(Put#(Bit#(16)));

  FIFO#(Bit#(16)) lfifo <- mkLFIFO;

  rule display_output;
    $display("FIFO element: %0d", lfifo.first);
    lfifo.deq;
  endrule

  return(fifoToPut(lfifo));

endmodule