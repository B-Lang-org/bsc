package Loopy;

import FIFO::*;
import FIFOF::*;

(* synthesize *)
module mkDesign (FIFO #(Bit #(8)));
  FIFO#(Bit#(8)) datafifo <- mkLoopy;
  return (datafifo);
endmodule

module mkLoopy(FIFO#(a)) provisos (Bits#(a,sa));

RWire#(a) enqw <- mkRWire;
RWire#(a) result <- mkRWire;
RWire#(PrimUnit) deqw <- mkRWire;
FIFOF#(a) the_fifof <- mkLFIFOF; // instantiate the Loopy fifo

rule doResult;  // set result in method
    result.wset(the_fifof.first());
endrule

rule doUpdate_enq;
  case (enqw.wget()) matches
    tagged Valid .r: 
        the_fifof.enq(r); 
    tagged Nothing:
      noAction;
  endcase
endrule

rule doUpdate_deq;
  if (isValid(deqw.wget))
    the_fifof.deq();
endrule

method Action clear();  // define the clear method
  the_fifof.clear();
endmethod: clear

method Action enq(val) if (the_fifof.notFull); // define the enqueue method
  enqw.wset(val);
endmethod: enq

method Action deq() if ((the_fifof.notEmpty));  // define the dequeue method
  deqw.wset(?); // I hate '?'.
endmethod: deq

method first() if (isValid(result.wget));  // define the first method. Read the result wire in method.
  return validValue(result.wget);
endmethod: first

endmodule: mkLoopy

endpackage: Loopy
