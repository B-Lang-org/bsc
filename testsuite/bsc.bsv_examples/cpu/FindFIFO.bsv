import FIFOF::*;

interface FindFIFO#(type t);
   method Action enq(t x);
   method Action deq();
   method t      first();
   method Action clear();
   method Bool   find(function Bool f(t x));
endinterface

module mkFindFIFO (FindFIFO#(t)) provisos (Bits#(t,szt));

   // one-element FIFO which can enq and deq simultaneously
   // and has exposed notEmpty signal
   FIFOF#(t) fifo();
   mkLFIFOF the_fifo(fifo);

   method enq(x)  = fifo.enq(x);
   method deq()   = fifo.deq();
   method first() = fifo.first();
   method clear() = fifo.clear();
   method find(f) = fifo.notEmpty ? f(fifo.first) : False;
endmodule

