import GetPut::*;
import FIFO::*;
import BypassFIFO::*;

// The bypass FIFO allows a deq from an empty FIFO
// as long as there is an enq in the same cycle.

// This means that the enq rule below should be
// more urgent than the get method which calls
// deq.

(* synthesize *)
module mkGetTest(Get#(Bit#(16)));

  FIFO#(Bit#(16)) bypass_fifo <- mkBypassFIFO;

  rule enq;
    bypass_fifo.enq(0);
    $display("Enq successful");
    $finish(0);    
  endrule

  return(fifoToGet(bypass_fifo));

endmodule