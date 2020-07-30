import FIFO::*;

import "BVI" FIFO2 = module mkBadFIFO (FIFO#(a)) provisos (Bits#(a,sa));
    parameter width = valueOf(sa);
    method enq((* reg *)D_IN) enable(ENQ) ready(FULL_N);
    method deq() enable(DEQ) ready(EMPTY_N);
    method (* reg *)D_OUT first ready(EMPTY_N);
    method clear() enable(CLR);
    schedule deq CF enq;
    schedule enq CF (deq, first);
    schedule first CF first;
    schedule (deq, enq) SB clear ;
    schedule clear SBR clear;
    schedule first SB (clear, deq) ;
  endmodule: mkBadFIFO


(* synthesize *)
module sysFIFOPush(FIFO#(Bit#(32)));

  FIFO#(Bit#(32)) a <- mkBadFIFO;
  FIFO#(Bit#(32)) b <- mkBadFIFO;
  
  rule push;
    b.enq(a.first);
    a.deq;
  endrule

  method enq = a.enq;
  method deq = b.deq;
  method first = b.first;
  method Action clear;
    a.clear;
    b.clear;
  endmethod

endmodule
