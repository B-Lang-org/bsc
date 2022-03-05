// Test the scheduling of modules from the library
// (that are not separately synthesized because they are polymorphic)

import SpecialFIFOs::*;
import FIFO::*;
import FIFOF::*;
import FIFOLevel::*;

// -------------------------

(* synthesize *)
module mkBypassFIFO_Bit32 (FIFO#(Bit#(32)));
   (* hide *)
   FIFO#(Bit#(32)) _ifc <- mkBypassFIFO;
   return _ifc;
endmodule

// -------------------------

(* synthesize *)
module mkBypassFIFOF_Bit32 (FIFOF#(Bit#(32)));
   (* hide *)
   FIFOF#(Bit#(32)) _ifc <- mkBypassFIFOF;
   return _ifc;
endmodule

// -------------------------

// mkSizedBypassFIFOF is tested in TbBypassFIFO
//   but it was not catching an issue in the scheduling of 'first'!
//   so explicitly test the schedule here, too

(* synthesize *)
module mkSizedBypassFIFOF_Bit32_8 (FIFOF#(Bit#(32)));
   (* hide *)
   FIFOF#(Bit#(32)) _ifc <- mkSizedBypassFIFOF(8);
   return _ifc;
endmodule

// -------------------------

// To test FIFOLevelIfc, we need to create a version that is bitifiable

interface FIFOLevel4#( type a_type, numeric type fifoDepth ) ;
   method Action enq( a_type x1 );
   method Action deq();
   method a_type first();
   method Action clear();

   method Bool notFull ;
   method Bool notEmpty ;

   method Bool isLessThan4 ();
   method Bool isGreaterThan4 ();
endinterface

(* synthesize *)
module mkBypassFIFOLevel_Bit32_8 (FIFOLevel4#(Bit#(32), 8));
   (* hide *)
   FIFOLevelIfc#(Bit#(32), 8) _ifc <- mkBypassFIFOLevel;

   method enq = _ifc.enq;
   method deq = _ifc.deq;
   method first = _ifc.first;
   method clear = _ifc.clear;
   method notFull = _ifc.notFull;
   method notEmpty = _ifc.notEmpty;

   method isLessThan4 = _ifc.isLessThan(4);
   method isGreaterThan4 = _ifc.isGreaterThan(4);
endmodule

// -------------------------
