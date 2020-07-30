// Simultaneous enqueue and dequeue when FIFO is empty

import FIFO::*;
import FIFOF::*;

(* synthesize *)
module mkDesign(FIFO#(Bit#(5)));

RWire#(Bit#(5)) enqw <- mkRWire;
RWire#(Bit#(5)) result <- mkRWire;
RWire#(PrimUnit) deqw <- mkRWire;

// instantiating unguarded FIFO
FIFOF#(Bit#(5)) the_fifof <- mkUGFIFOF;

// print first element condition checking
rule doResult;
  if (the_fifof.notEmpty)
    result.wset(the_fifof.first());
  else case (enqw.wget()) matches
    tagged Valid .r:
      result.wset(r);
    tagged Nothing:
      noAction;
    endcase
endrule
// enq when condition is true
rule doUpdate_enq;
  case (enqw.wget()) matches
    tagged Valid .r: 
      if (the_fifof.notEmpty || !isValid(deqw.wget))
        the_fifof.enq(r); 
    tagged Nothing:
      noAction;
  endcase
endrule
// does deq when condition is true
rule doUpdate_deq;
  if (isValid(deqw.wget) && the_fifof.notEmpty)
    the_fifof.deq();
endrule
// to clear FIFO
method Action clear();
  the_fifof.clear();
endmethod: clear
// to enq into a FIFO
method Action enq(val) if (the_fifof.notFull);
  enqw.wset(val);
endmethod: enq

// setting the conditions for deq
method Action deq() if ((the_fifof.notEmpty || isValid (enqw.wget())));
  deqw.wset(?); 
endmethod: deq

// prints the first element of the FIFO
method first() if (isValid(result.wget));
  return validValue(result.wget);
endmethod: first

endmodule
