package BypassFIFO;

import FIFO::*;

// ================================================================
// This package implements "bypass FIFOs", in which the ENQ and
// {FIRST,DEQ} methods have different scheduling from conventional
// FIFOS.
//
// ***** WARNING
// ***** Bypass FIFOs have combinational paths from the ENQ data-in to
// ***** the FIRST data-out, because data can be bypassed across the FIFO.
// ***** This affects path lengths, and therefore can affect timing closure.
// ***** Be aware of this, when using Bypass FIFOs!
//
// The following table summarizes the properties of ordinary
// and bypass fifos.
//
//                         |       FIFO        |    BypassFIFO    |
//  Fifo depth             |    1        >1    |   1         >1   |
//                         +-------------------+------------------+
//  Empty                  |    E         E    | E < FD    E < FD |
//  Neither Empty nor Full |   n.a.    FD < E  |  n.a.     E < FD |
//  Full                   | FD < E    FD < E  |   FD        FD   |
//                         +-------------------+------------------+
//
//  Legend:
//  - E, F, D stand for the ENQ, FIRST and DEQ methods
//  - n.a.    means "not applicable"
//
// In a conventional FIFO,
//  - you can only ENQ if Empty (can't {FIRST,DEQ})
//  - you can simultaneously ENQ and {DEQ,FIRST} if Full, and
//    it is as if you do {DEQ,FIRST} followed by ENQ
//  - Every item sits in the FIFO for at least 1 tick
//
// In a Bypass FIFO,
//  - you can only {FIRST,DEQ} if Full (can't ENQ)
//  - you can simultaneously ENQ and {DEQ,FIRST} if Empty, and
//    it is as if you do ENQ followed by {DEQ,FIRST}.  In this
//    case, the newly enqueued item is "bypassed" directly across
//    to the {FIRST,DEQ} operation, i.e., the item flies through
//    with zero latency (combinationally).
//
// If either FIFO is of depth > 1, and it is neither Empty nor Full,
// then although the scheduling is FD < E in one case and E < FD in
// the other, the external behavior will be the same (the operations
// commute).
//
// If either FIFO is of depth 1, the 'Neither Empty nor Full' case
// is impossible.

// ================================================================
// Note: the modules below are polymorphic, and so can't be
// synthesized separately.  The following template shows how
// you can synthesize a non-polymorphic instantiation.
//
//    (* synthesize *)
//    module mkBypassFIFO_int (FIFO#(int));
//       FIFO#(int) f <- mkBypassFIFO2;    // 2-element BypassFIFO
//       return f;
//    endmodule: mkBypassFIFO_int

// ================================================================
// The following is a 1-element "bypass FIFO".

module mkBypassFIFO1 (FIFO#(t))
   provisos (Bits#(t,sizet));

   // STATE ----------------
   
   // The fifo
   Reg#(t)         regh      <- mkRegU;
   Reg#(Bool)      fifoFull  <- mkReg (False);

   // Method signals
   RWire#(t)       rw_enq    <- mkRWire;
   RWire#(Bit#(0)) rw_deq    <- mkRWire;

   // RULES ----------------
   
   // Note: no rule needed for enq_and_deq_on_Empty, since
   // fifoState remains Empty

   // Note: enq_and_deq_on_Full is disallowed

   rule enq_only_on_Empty
           (rw_enq.wget matches tagged Valid .v &&&
            rw_deq.wget matches tagged Invalid  &&&
            !fifoFull);
       regh      <= v;
       fifoFull  <= True;
   endrule

   rule deq_only_on_Full
           (rw_enq.wget matches tagged Invalid  &&&
            rw_deq.wget matches tagged Valid .* &&&
            fifoFull);
       fifoFull <= False;
   endrule

   t new_first = (rw_enq.wget matches tagged Valid .v &&& (! fifoFull)
                 ? v
                 : regh);

   // INTERFACE ----------------
   
   method Action enq(v) if (!fifoFull);
       rw_enq.wset(v);
   endmethod

   method Action deq() if (fifoFull || isValid (rw_enq.wget));
       rw_deq.wset(?);
   endmethod

   method first()      if (fifoFull || isValid (rw_enq.wget));
       return new_first;
   endmethod

   method Action clear();
      fifoFull <= False;
   endmethod

endmodule: mkBypassFIFO1

// ================================================================
// The following is a 2-element "bypass FIFO".

typedef enum { Zero, One, Two } Fifo2State
        deriving (Bits, Eq);

module mkBypassFIFO2 (FIFO#(t))
   provisos (Bits#(t,sizet));

   // STATE ----------------
   
   // The fifo
   Reg#(t)          regh      <- mkRegU;
   Reg#(t)          regt      <- mkRegU;
   Reg#(Fifo2State) fifo2State <- mkReg (Zero);

   // Method signals
   RWire#(t)       rw_enq    <- mkRWire;
   RWire#(Bit#(0)) rw_deq    <- mkRWire;

   // RULES ----------------
   
   // Note: no rule needed for enq_and_deq_on_Zero, since
   // fifo2State remains Zero

   rule enq_and_deq_on_One
           (rw_enq.wget matches tagged Valid .v &&&
            rw_deq.wget matches tagged Valid .* &&&
            fifo2State == One);
       regh <= v;
   endrule

   rule enq_only_on_Zero
           (rw_enq.wget matches tagged Valid .v &&&
            rw_deq.wget matches tagged Invalid  &&&
            fifo2State == Zero);
       regh      <= v;
       fifo2State <= One;
   endrule

   rule enq_only_on_One
           (rw_enq.wget matches tagged Valid .v &&&
            rw_deq.wget matches tagged Invalid  &&&
            fifo2State == One);
       regt      <= v;
       fifo2State <= Two;
   endrule

   rule deq_only_on_One
           (rw_enq.wget matches tagged Invalid  &&&
            rw_deq.wget matches tagged Valid .* &&&
            fifo2State == One);
       fifo2State <= Zero;
   endrule

   rule deq_only_on_Two
           (rw_enq.wget matches tagged Invalid  &&&
            rw_deq.wget matches tagged Valid .* &&&
            fifo2State == Two);
       regh      <= regt;
       fifo2State <= One;
   endrule

   t new_first = (rw_enq.wget matches tagged Valid .v &&& (fifo2State == Zero)
                 ? v
                 : regh);

   // INTERFACE ----------------
   
   method Action enq(v) if (fifo2State != Two);
       rw_enq.wset(v);
   endmethod

   method Action deq() if ((fifo2State != Zero) || isValid (rw_enq.wget));
       rw_deq.wset(?);
   endmethod

   method first()      if ((fifo2State != Zero) || isValid (rw_enq.wget));
       return new_first;
   endmethod

   method Action clear();
      fifo2State <= Zero;
   endmethod

endmodule: mkBypassFIFO2

endpackage:  BypassFIFO
