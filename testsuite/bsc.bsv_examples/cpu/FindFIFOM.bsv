/*----------------------------------------------------------------------------

FindFIFOM
 
This version of the find FIFO returns more than just a Bool.
It also returns data.  This can be used to bypass values.

-----------------------------------------------------------------------------*/

import FIFOF::*;

interface FindFIFOM#(type t1, type t2);
   method Action enq(t1 x);
   method Action deq();
   method t1     first();
   method Action clear();
   method Maybe#(t2) find(function Maybe#(t2) f(t1 x));
endinterface

module mkFindFIFOM (FindFIFOM#(t1,t2)) provisos (Bits#(t1,szt1));

   // one-element FIFO which can enq and deq simultaneously
   // and has exposed notEmpty signal
   FIFOF#(t1) fifo();
   mkLFIFOF the_fifo(fifo);

   method enq(x)  = fifo.enq(x);
   method deq()   = fifo.deq();
   method first() = fifo.first();
   method clear() = fifo.clear();
   method find(f) = fifo.notEmpty ? f(fifo.first) : Invalid;
endmodule

