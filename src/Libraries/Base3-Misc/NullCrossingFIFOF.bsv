package NullCrossingFIFOF;

import FIFOF::*;
import Clocks::*;
import GetPut::*;

interface CrossingFIFOF#(type a);
   interface FIFOF#(a) fifo;
   (*always_ready*)
   method Bool allowCclock;
endinterface

module mkCtoUNullCrossingFIFOF#(Clock sClk, Reset sRstn, Clock dClk, Reset dRstn)(CrossingFIFOF#(a))
   provisos (Bits#(a,sa));

   CrossingReg#(a)    r <- mkNullCrossingRegU(dClk, clocked_by sClk, reset_by sRstn);

   CrossingReg#(Bool) a <- mkNullCrossingRegA(dClk, False, clocked_by sClk, reset_by sRstn);
   CrossingReg#(Bool) b <- mkNullCrossingRegA(sClk, False, clocked_by dClk, reset_by dRstn);
   CrossingReg#(Bool) c <- mkNullCrossingRegA(sClk, False, clocked_by dClk, reset_by dRstn);
   CrossingReg#(Bool) d <- mkNullCrossingRegA(sClk, False, clocked_by dClk, reset_by dRstn);

   rule writeB (True);
      b <= a.crossed();
   endrule

   rule writeD (d != c);
      d <= c;
   endrule

   interface FIFOF fifo;
      method notFull = (a == d.crossed());

      method Action enq(x) if (a == d.crossed());
	 r <= x;
	 a <= !a;
      endmethod

      method notEmpty = (b != c);

      method first () if (b != c) = r.crossed();

      method Action deq () if (b != c);
	 c <= b;
      endmethod

      // disable, at least for now:
      method Action clear() if (False) = noAction;
   endinterface

   // Clocks allowed when fifo is empty -- allowing an enq from the C-clock domain
   method allowCclock  = (a.crossed==d);
endmodule

module mkUtoCNullCrossingFIFOF#(Clock sClk, Reset sRstn, Clock dClk, Reset dRstn)(CrossingFIFOF#(a))
   provisos (Bits#(a,sa));

   CrossingReg#(a)    r <- mkNullCrossingRegU(dClk, clocked_by sClk, reset_by sRstn);

   CrossingReg#(Bool) a <- mkNullCrossingRegA(dClk, False, clocked_by sClk, reset_by sRstn);
   CrossingReg#(Bool) b <- mkNullCrossingRegA(dClk, False, clocked_by sClk, reset_by sRstn);
   CrossingReg#(Bool) c <- mkNullCrossingRegA(sClk, False, clocked_by dClk, reset_by dRstn);
   Reg#(Bool)         d <- mkRegA                  (False, clocked_by sClk, reset_by sRstn);

   rule writeB (b != a);
      b <= a;
   endrule

   rule writeD (d != c.crossed());
      d <= c.crossed();
   endrule

   interface FIFOF fifo;
      method notFull = (a == d);

      method Action enq(x) if (a == d);
	 r <= x;
	 a <= !a;
      endmethod

      method notEmpty = (b.crossed() != c);

      method first () if (b.crossed() != c) = r.crossed();

      method Action deq () if (b.crossed() != c);
	 c <= b.crossed();
      endmethod

      // disable, at least for now:
      method Action clear() if (False) = noAction;
   endinterface

   // Allow clocks only when data is present in the C-clock domain
   //  -- a very strict stall method -- equivalent to notEmpty
   method allowCclock = (c.crossed != b);
endmodule

// Typeclass instances
instance ToPut#(CrossingFIFOF#(t), t);
   function Put#(t) toPut(CrossingFIFOF#(t) f);
      return (interface Put;
                 method Action put(t val) = f.fifo.enq(val);
              endinterface);
   endfunction
endinstance

instance ToGet#(CrossingFIFOF#(t), t);
   function Get#(t) toGet(CrossingFIFOF#(t) f);
      return (interface Get;
                 method ActionValue#(t) get();
                    f.fifo.deq();
                    return f.fifo.first();
                 endmethod
              endinterface);
   endfunction
endinstance


//////////////////////////////////////////////////////////////////////////////
interface SceMiCrossingReg#(type a);
   interface Reg#(a) regifc;
   (*always_ready*)
   method Bool writtenPulse;
   (*always_ready*)
   method Bool readPulse;
   (*always_ready*)
   method Bool allowCclock;
endinterface


module mkUtoCNullCrossingReg#(Clock sClk, Reset sRstn, Clock dClk, Reset dRstn)(SceMiCrossingReg#(a))
   provisos (Bits#(a,sa));

   CrossingReg#(a)     r <- mkNullCrossingRegU      (dClk, clocked_by sClk, reset_by sRstn);

   Reg#(Bool)         a <- mkRegA                  (False, clocked_by sClk, reset_by sRstn);
   CrossingReg#(Bool) b <- mkNullCrossingRegA(dClk, False, clocked_by sClk, reset_by sRstn);
   CrossingReg#(Bool) c <- mkNullCrossingRegA(sClk, False, clocked_by dClk, reset_by dRstn);
   Reg#(Bool)         d <- mkRegA                  (False, clocked_by sClk, reset_by sRstn);

   (* no_implicit_conditions, fire_when_enabled *)
   rule updateStateU2 (True);
      b <= a;
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule trackC (True);
      c <= b.crossed;
   endrule
   (* no_implicit_conditions, fire_when_enabled *)
   rule trackD (True);
      d <= c.crossed();
   endrule

   interface Reg regifc;
      method Action _write (a x) if (a == d);
         r <= x;
         a <= !a;
      endmethod
      // Always ready
      method a _read ();
         return r.crossed;
      endmethod
   endinterface

   // Allow clocks only for one cycle when is present.
   method Bool allowCclock        = (b != c.crossed);
   method Bool writtenPulse       = (a != b);
   method Bool readPulse   = (c.crossed != d);
endmodule


endpackage
