import GetPut::*;
import FIFO::*;
import BypassFIFO::*;

(* synthesize *)
module mkPutTest(Get#(Bit#(16)));

  FIFO#(Bit#(16)) bypass_fifo <- mkBypassFIFO1;

  rule enq;
    bypass_fifo.enq(0);
    $display("Enq successful");
    $finish(0);    
  endrule

  return(fifoToGet(bypass_fifo));

endmodule

