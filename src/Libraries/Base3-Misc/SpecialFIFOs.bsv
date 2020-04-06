package SpecialFIFOs;

// ================================================================
//
// This package contains several FIFO variants.  The two main variants
// are 1-element FIFOs that both allow simultaneous enq and deq, but
// with different scheduling semantics. These are useful for achieving
// latency and throughput goals in certain designs
//
// Scheduling semantics
//   - a PipelineFIFO allows a simultaneous enq and deq when full,
//     behaving like a deq followed by enq, so that the value already
//     in the FIFO is returned by the deq, and the new enq'd value
//     then occupies the FIFO, and the FIFO remains full.
//     Note: every value spends at least 1 cycle in the FIFO
//
//     Thus, this FIFO is useful for "registered" data,
//     where the expectation is a latency of 1 tick due to registering.
//
//   - a BypassFIFO allows a simultaneous enq and deq when empty,
//     behaving like an enq followed by deq so that the new value
//     being enq'd "flies through" (or is "bypassed through") the FIFO
//     and is returned by the deq operation, and the FIFO remains empty.
//     Note: in this situation, the value spends 0 cycles in the FIFO
//     Note: there is a combinational path from enq'd data to deq'd data
//
//     Thus, this FIFO is useful for 0-tick latency situations
//
//   The BSV library provides 'mkLFIFOF' also known as a "loopy FIFO"
//       and this is just a 1-element PipelineFIFO (with guarded ends)
//
// ================================================================

import FIFO::*;
import FIFOF::*;
import FIFOLevel::*;
import RevertingVirtualReg::*;


export mkPipelineFIFO;
export mkPipelineFIFOF;

export mkBypassFIFO;
export mkBypassFIFOF;

export mkDFIFOF;
export mkSizedDFIFOF;

export mkSizedBypassFIFOF;
export mkBypassFIFOLevel;

// ================================================================
// 1-element "pipeline FIFO"
// It's a 1-element FIFO (register with Valid/Invalid tag bit), where
//   - if empty, can only enq, cannot deq, leaving it full
//   - if full, can
//     - either just deq, leaving it empty
//     - or deq and enq simultaneously (logically: deq before enq), leaving it full

module mkPipelineFIFO (FIFO#(a))
   provisos (Bits#(a,sa));

   (* hide *) FIFOF#(a) _ifc <- mkPipelineFIFOF;

   // return fifofToFifo(_ifc)
   method enq = _ifc.enq;
   method deq = _ifc.deq;
   method first = _ifc.first;
   method clear = _ifc.clear;

endmodule: mkPipelineFIFO

module mkPipelineFIFOF (FIFOF#(a))
   provisos (Bits#(a,sa));

   // STATE ----------------

   Reg#(Maybe#(a)) rv[3] <- mkCReg(3, tagged Invalid);

   // INTERFACE ----------------

   Bool enq_ok = ! isValid(rv[1]);
   Bool deq_ok = isValid(rv[0]);

   method notFull = enq_ok;

   method Action enq(v) if (enq_ok);
      rv[1] <= tagged Valid v;
   endmethod

   method notEmpty = deq_ok;

   method Action deq() if (deq_ok);
      rv[0] <= tagged Invalid;
   endmethod

   method first() if (rv[0] matches tagged Valid .v); // deq_ok
      return v;
   endmethod

   method Action clear();
      rv[2] <= tagged Invalid;
   endmethod

endmodule

// ================================================================
// 1-element "bypass FIFO".
// It's a 1-element FIFO (register with Valid/Invalid tag bit), where
//   - if full, can only deq, cannot enq, leaving it empty
//   - if empty, can
//     - either just enq, leaving it full
//     - or enq and deq simultaneously (logically: enq before deq), leaving it empty

module mkBypassFIFO (FIFO#(a))
   provisos (Bits#(a,sa));

   (* hide *) FIFOF#(a) _ifc <- mkBypassFIFOF;

   // return fifofToFifo(_ifc)
   method enq = _ifc.enq;
   method deq = _ifc.deq;
   method first = _ifc.first;
   method clear = _ifc.clear;

endmodule

module mkBypassFIFOF (FIFOF#(a))
   provisos (Bits#(a,sa));

   // STATE ----------------

   Reg#(Maybe#(a)) rv[3] <- mkCReg(3, tagged Invalid);

   // INTERFACE ----------------

   Bool enq_ok = ! isValid(rv[0]);
   Bool deq_ok = isValid(rv[1]);

   method notFull = enq_ok;

   method Action enq(v) if (enq_ok);
      rv[0] <= tagged Valid v;
   endmethod

   method notEmpty = deq_ok;

   method Action deq() if (deq_ok);
      rv[1] <= tagged Invalid;
   endmethod

   method first() if (rv[1] matches tagged Valid .v); // deq_ok
      return v;
   endmethod

   method Action clear();
      rv[2] <= tagged Invalid;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
/// A FIFOF with unguarded deq and first methods (thus they have no
/// implicit conditions).
/// The 'first' method returns a specified "default" value when the
/// FIFO is empty.
////////////////////////////////////////////////////////////////////////////////

module mkDFIFOF#(a dflt) (FIFOF#(a))
   provisos (Bits#(a,sa));
   (*hide*)
   let _ifc <- mkSizedDFIFOF(2, dflt);
   return _ifc;
endmodule

module mkSizedDFIFOF#(Integer n, a dflt) (FIFOF#(a))
   provisos (Bits#(a,sa));

   // If the queue contains n elements, they are in q[0]..q[n-1].  The head of
   // the queue (the "first" element) is in q[0], the tail in q[n-1].

   Reg#(a) q[n];
   for (Integer i=0; i<n; i=i+1)
      q[i] <- mkReg(dflt);
   SCounter cntr <- mkSCounter(n);

   PulseWire enqueueing <- mkPulseWire;
   Wire#(a)      x_wire <- mkWire;
   PulseWire dequeueing <- mkPulseWire;

   let empty = cntr.isEq(0);
   let full  = cntr.isEq(n);

   rule incCtr (enqueueing && !dequeueing);
      cntr.incr;
      cntr.setNext(x_wire, q);
   endrule
   rule decCtr (dequeueing && !enqueueing);
      for (Integer i=0; i<n; i=i+1)
	 q[i] <= (i==(n - 1) ? dflt : q[i + 1]);
      cntr.decr;
   endrule
   rule both (dequeueing && enqueueing);
      for (Integer i=0; i<n; i=i+1)
	 if (!cntr.isEq(i + 1)) q[i] <= (i==(n - 1) ? dflt : q[i + 1]);
      cntr.set(x_wire, q);
   endrule

   method Action deq;
      if (!empty) dequeueing.send;
   endmethod

   method first; // no implicit conditions on first!!!
      return q[0];
   endmethod

   method Action enq(x) if (!full);
      enqueueing.send;
      x_wire <= x;
   endmethod

   method notEmpty = !empty;
   method notFull  = !full;

   method Action clear;
      cntr.clear;
   endmethod
endmodule

interface SCounter;
   method Action incr;
   method Action decr;
   method Bool isEq(Integer n);
   method Action setNext (b value, Reg#(b) as[]);
   method Action set (b value, Reg#(b) as[]);
   method Action clear;
endinterface

module mkSCtr#(Reg#(UInt#(s)) c)(SCounter);
   method Action incr; c <= c+1; endmethod
   method Action decr; c <= c-1; endmethod
   method isEq(n) = (c==fromInteger(n));
   method Action setNext (b value, Reg#(b) as[]); as[c] <= value; endmethod
   method Action set (b value, Reg#(b) as[]); as[c-1] <= value; endmethod
   method Action clear; c <= 0; endmethod
endmodule

// A counter which can count up to m inclusive (m known at compile time):
module mkSCounter#(Integer m)(SCounter);
   let _i = ?;
   if      (m<2)      begin Reg#(UInt#(1))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<4)      begin Reg#(UInt#(2))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<8)      begin Reg#(UInt#(3))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<16)     begin Reg#(UInt#(4))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<32)     begin Reg#(UInt#(5))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<64)     begin Reg#(UInt#(6))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<128)    begin Reg#(UInt#(7))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<256)    begin Reg#(UInt#(8))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<512)    begin Reg#(UInt#(9))  r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<1024)   begin Reg#(UInt#(10)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<2048)   begin Reg#(UInt#(11)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<4096)   begin Reg#(UInt#(12)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<8192)   begin Reg#(UInt#(13)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<16384)  begin Reg#(UInt#(14)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<32768)  begin Reg#(UInt#(15)) r <- mkReg(0); _i <- mkSCtr(r); end
   else if (m<65536)  begin Reg#(UInt#(16)) r <- mkReg(0); _i <- mkSCtr(r); end
   return _i;
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkSizedBypassFIFOF#(Integer n)(FIFOF#(a))
   provisos (Bits#(a,sa));

   FIFOF#(a) ff <- mkUGSizedFIFOF(n);

   RWire#(a) enqw <- mkRWire;
   Reg#(Bool) firstValid <- mkRevertingVirtualReg(True);
   PulseWire dequeueing <- mkPulseWire;

   let empty = !ff.notEmpty;
   let full  = !ff.notFull;
   let enqueueing = isValid(enqw.wget);
   let bypassing = (enqueueing && dequeueing && empty);

   rule enqueue (enqueueing && !bypassing);
      ff.enq(validValue(enqw.wget));
   endrule

   rule dequeue (dequeueing && !empty);
      ff.deq;
   endrule

   method Action deq if (!empty || enqueueing);
      dequeueing.send;
      firstValid <= False;
   endmethod

   method first if (firstValid && (!empty || enqueueing));
      return (empty ? validValue(enqw.wget) : ff.first);
   endmethod

   method Action enq(x) if (!full);
      enqw.wset(x);
   endmethod

   method Action clear;
      ff.clear;
   endmethod

   method notEmpty = ff.notEmpty;
   method notFull  = ff.notFull;
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkBypassFIFOLevel(FIFOLevelIfc#(a, fifoDepth))
   provisos( Bits#(a, sa), Log#(TAdd#(fifoDepth,1), cntSize));

   Integer ififoDepth = (valueOf(fifoDepth) < 3 ?
			 (error ("mkFIFOLevel: fifoDepth must be greater than 2. " +
                                 "Specified depth is " +
				 integerToString(valueOf(fifoDepth)) +
				 "." )) : valueOf(fifoDepth));

   FIFOF#(a) fifof <- mkSizedBypassFIFOF(ififoDepth);

   Reg#(UInt#(cntSize)) count       <- mkReg(0);
   Reg#(Bool)           levelsValidEnq <- mkRevertingVirtualReg(True);
   Reg#(Bool)           levelsValidDeq <- mkRevertingVirtualReg(True);
   Reg#(Bool)           levelsValidClr <- mkRevertingVirtualReg(True);
   PulseWire      do_enq      <- mkPulseWire;
   PulseWire      do_deq      <- mkPulseWire;
   PulseWire      do_clr      <- mkPulseWire;

   Bool levelsValid = levelsValidEnq && levelsValidDeq && levelsValidClr;

   rule do_incr (do_enq && !do_deq && !do_clr);
      count <= count + 1;
   endrule

   rule do_decr (!do_enq && do_deq && !do_clr);
      count <= count - 1;
   endrule

   rule do_clear (do_clr);
      count <= 0;
   endrule

   method Action enq(a value);
      fifof.enq(value);
      levelsValidEnq <= False;
      do_enq.send;
   endmethod

   method Action deq;
      fifof.deq;
      levelsValidDeq <= False;
      do_deq.send;
   endmethod

   method first = fifof.first;
   method Action clear;
      fifof.clear;
      levelsValidClr <= False;
      do_clr.send;
   endmethod

   method notFull  = fifof.notFull ;
   method notEmpty = fifof.notEmpty;

   method Bool isLessThan (Integer c) if (levelsValid) ;
      return rangeTest(count, c, \< , 1, ififoDepth  , "isLessThan" ) ;
   endmethod

   method Bool isGreaterThan (Integer c) if (levelsValid) ;
      return rangeTest(count, c, \> , 0, ififoDepth -1  , "isGreaterThan" ) ;
   endmethod

endmodule

// Common function to test the validity arguments to methods
function Bool rangeTest( UInt#(cntSz) value,
                        Integer comp,
                        function Bool foperation(UInt#(cntSz) a,
                                                 UInt#(cntSz) b ),
                           Integer minValue,
                           Integer maxValue,
                           String methodName );

     return ((comp >= minValue) && (comp <= maxValue )) ?
                           (foperation (value,  fromInteger( comp ))) :
                           error( "Argument of " + methodName + " must be in the range of " +
                                 integerToString( minValue) +
                                 " to " +
                                 integerToString( maxValue ) +
                                 "; " +
                                 integerToString( comp ) +
                                 " is out of range.") ;
endfunction

endpackage
