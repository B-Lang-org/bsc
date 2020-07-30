/*----------------------------------------------------------------------------

FindFIFO3
 
This file shows an alternate way to define the FindFIFO.
Instead of the find function dynamically taking an argument,
it seems more intuitive to provide the find function as
an instantiation paramater.  In separate compilation, this
affects the ports on the FIFO module and where the find
logic is located.

-----------------------------------------------------------------------------*/

import FIFOF::*;

interface FindFIFO#(type t1, type t2);
   method Action enq(t1 x);
   method Action deq();
   method t1     first();
   method Action clear();
   method Bool   find(t2 y);
endinterface

// parser bug requires the second "f"
module mkFindFIFO#(function Bool f(t1 a, t2 b)) (FindFIFO#(t1,t2))
 provisos (Bits#(t1,szt1));

   // one-element FIFO which can enq and deq simultaneously
   // and has exposed notEmpty signal
   FIFOF#(t1) fifo();
   mkLFIFOF the_fifo(fifo);

   method enq(x)  = fifo.enq(x);
   method deq()   = fifo.deq();
   method first() = fifo.first();
   method clear() = fifo.clear();
   method find(y) = fifo.notEmpty ? f(fifo.first, y) : False;
endmodule

