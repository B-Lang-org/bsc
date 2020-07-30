import GetPut::*;
import FIFO::*;

(* synthesize *)
module mkPutTest(Put#(Bit#(16)));

  FIFO#(Bit#(16)) lfifo <- mkLFIFO;

  rule display_output;
    $display("FIFO element: %0d", lfifo.first);
    lfifo.deq;
  endrule

  return(fifoToPut(lfifo));

endmodule

