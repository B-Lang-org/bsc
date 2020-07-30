import GetPut::*;
import FIFO::*;

// The "loopy" FIFO allows an enq to a full FIFO
// as long as there is a deq in the same
// cycle.

// This means that the display_output rule that
// calls deq should be more urgent than the put
// method which calls enq.

// In addition, the rule and method conflict
// on the count register.

(* synthesize *)
module mkPutTest2(Put#(Bit#(16)));

  FIFO#(Bit#(16)) lfifo <- mkLFIFO;
  Reg#(UInt#(8))  count <- mkReg(0);

  rule display_output;
    $display("FIFO element: %0d", lfifo.first);
    $display("count = %0d", count);
    lfifo.deq;
    count <= count - 1;
  endrule

  method Action put(Bit#(16) x);
    lfifo.enq(x);
    count <= count + 1;
  endmethod

endmodule