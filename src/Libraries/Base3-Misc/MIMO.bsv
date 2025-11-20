////////////////////////////////////////////////////////////////////////////////
//  Filename      : MIMO.bsv
//  Description   : Multiple-In Multiple-Out
////////////////////////////////////////////////////////////////////////////////
package MIMO;

// Notes :
// - This module works like a FIFO, but for arbitrary amounts of the base object type.
// - The clear method overrides the effects of enq and deq.

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Vector            ::*;
import BUtils            ::*;
import FIFOF             ::*;
import BRAMFIFO          ::*;
import Counter           ::*;

////////////////////////////////////////////////////////////////////////////////
/// Exports
////////////////////////////////////////////////////////////////////////////////
export LUInt(..);
export MIMOConfiguration(..);
export MIMO(..);
export mkMIMO;
export mkMIMOV;
export mkMIMOReg;

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typedef UInt#(TLog#(TAdd#(n, 1)))     LUInt#(numeric type n);

typedef struct {
   Bool         unguarded;
   Bool         bram_based;
} MIMOConfiguration deriving (Eq);

instance DefaultValue#(MIMOConfiguration);
   defaultValue = MIMOConfiguration {
      unguarded:  False,
      bram_based: False
      };
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////
interface MIMO#(  numeric type max_in  // maximum number of objects enqueued in one cycle
                , numeric type max_out // maximum number of objects dequeued in one cycle
                , numeric type size    // total size of internal storage
                , type t               // object type
                );
   method    Action                      enq(LUInt#(max_in) count, Vector#(max_in, t) data);
   method    Vector#(max_out, t)         first;
   method    Action                      deq(LUInt#(max_out) count);

   (* always_ready *)
   method    Bool                        enqReady;
   (* always_ready *)
   method    Bool                        enqReadyN(LUInt#(max_in) count);
   (* always_ready *)
   method    Bool                        deqReady;
   (* always_ready *)
   method    Bool                        deqReadyN(LUInt#(max_out) count);

   (* always_ready *)
   method    LUInt#(size)                count;
   method    Action                      clear;
endinterface

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of BRAM based version
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkMIMOBram#(MIMOConfiguration cfg)(MIMO#(max_in, max_out, size, t))
   provisos (  Bits#(t, st)               // object must have bit representation
	     , Add#(__f, 1, st)           // object is at least 1 byte in size
	     , Add#(2, __a, size)         // must have at least 2 elements of storage
	     , Add#(__b, max_in, size)    // the max enqueued amount must be less than or equal to the full storage
	     , Add#(__c, max_out, size)   // the max dequeued amount must be less than or equal to the full storage
             , Mul#(st, size, total)      // total bits of storage
             , Mul#(st, max_in, intot)    // total bits to be enqueued
             , Mul#(st, max_out, outtot)  // total bits to be dequeued
             , Add#(__d, outtot, total)   // make sure the number of dequeue bits is not larger than the total storage
	     , Max#(max_in, max_out, max) // calculate the max width of the memories
	     , Div#(size, max, em1)       // calculate the number of entries for each memory required
	     , Add#(em1, 1, e)
	     , Add#(__e, max_out, max)
             );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Vector#(max, FIFOF#(t))         vfStorage           <- replicateM(mkSizedBRAMFIFOF(valueOf(e)));
   Counter#(32)                    rDataCount          <- mkCounter(0);

   Reg#(LUInt#(max))               rWriteIndex         <- mkReg(0);
   Reg#(LUInt#(max))               rReadIndex          <- mkReg(0);

   Vector#(max, RWire#(Bool))      vrwDeqFifo          <- replicateM(mkRWire);
   Vector#(max, RWire#(t))         vrwEnqFifo          <- replicateM(mkRWire);

   RWire#(LUInt#(size))            rwDeqCount          <- mkRWire;
   RWire#(LUInt#(size))            rwEnqCount          <- mkRWire;
   RWire#(Bit#(intot))             rwEnqData           <- mkRWire;
   PulseWire                       pwClear             <- mkPulseWire;

   ////////////////////////////////////////////////////////////////////////////////
   /// Functions
   ////////////////////////////////////////////////////////////////////////////////
   function t getFirst(FIFOF#(t) ifc);
      return ifc.first();
   endfunction

   function Action doEnq(Bool doit, FIFOF#(t) ifc, t datain);
      action
	 if (doit) ifc.enq(datain);
      endaction
   endfunction

   function Action doDeq(Bool doit, FIFOF#(t) ifc);
      action
	 if (doit) ifc.deq();
      endaction
   endfunction

   function Vector#(max, Bool) createMask(LUInt#(max) count);
      Bit#(max) v = (1 << count) - 1;
      return unpack(v);
   endfunction

   function Vector#(v, el) rotateRBy(Vector#(v, el) vect, UInt#(logv) n)
      provisos(Log#(v, logv));
      return reverse(rotateBy(reverse(vect), n));
   endfunction

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   Rules d =
   rules
      (* aggressive_implicit_conditions *)
      rule dequeue if (rwDeqCount.wget matches tagged Valid .dcount);
	 Vector#(max, Bool) deqDoIt = rotateBy(createMask(cExtend(dcount)), cExtend(rReadIndex));
	 for(Integer i = 0; i < valueOf(max); i = i + 1) begin
	    if (deqDoIt[i]) vrwDeqFifo[i].wset(True);
	 end

	 rDataCount.dec(cExtend(dcount));

	 UInt#(32) ridx = cExtend(rReadIndex);
	 UInt#(32) dcnt = cExtend(dcount);
	 if ((ridx + dcnt) >= fromInteger(valueOf(max)))
	    rReadIndex <= rReadIndex - fromInteger(valueOf(max)) + cExtend(dcount);
	 else
	    rReadIndex <= rReadIndex + cExtend(dcount);
      endrule

      (* aggressive_implicit_conditions *)
      rule enqueue if (rwEnqCount.wget matches tagged Valid .ecount &&&
		      rwEnqData.wget matches tagged Valid .edata
		      );
	 Vector#(max, t)    enqData = rotateBy(unpack(cExtend(edata)), cExtend(rWriteIndex));
	 Vector#(max, Bool) enqDoIt = rotateBy(createMask(cExtend(ecount)), cExtend(rWriteIndex));

	 for(Integer i = 0; i < valueOf(max); i = i + 1) begin
	    if (enqDoIt[i]) vrwEnqFifo[i].wset(enqData[i]);
	 end

	 rDataCount.inc(cExtend(ecount));

	 UInt#(32) widx = cExtend(rWriteIndex);
	 UInt#(32) ecnt = cExtend(ecount);
	 if ((widx + ecnt) >= fromInteger(valueOf(max)))
	    rWriteIndex <= rWriteIndex - fromInteger(valueOf(max)) + cExtend(ecount);
	 else
	    rWriteIndex <= rWriteIndex + cExtend(ecount);
      endrule
   endrules;

   Rules re = emptyRules;
   for(Integer i = 0; i < valueOf(max); i = i + 1) begin
      re = rJoinConflictFree(re,
	 rules
	    rule enqueue_fifo if (vrwEnqFifo[i].wget matches tagged Valid .enqdata);
	       vfStorage[i].enq(enqdata);
	    endrule
	 endrules
	 );
   end

   Rules rd = emptyRules;
   for(Integer i = 0; i < valueOf(max); i = i + 1) begin
      rd = rJoinConflictFree(rd,
	 rules
	    rule dequeue_fifo if (vrwDeqFifo[i].wget matches tagged Valid .*);
	       vfStorage[i].deq();
	    endrule
	 endrules
	 );
   end

   Rules r = rJoinConflictFree(rd, re);
   r = rJoin(d, r);
   r = rJoinPreempts(
		     rules
			(* fire_when_enabled *)
			rule clear if (pwClear);
			   function Action getClear(FIFOF#(t) ifc) = ifc.clear();
			   rDataCount.setF(0);
			   rWriteIndex <= 0;
			   rReadIndex <= 0;
			   joinActions(map(getClear, vfStorage));
			endrule
		     endrules, r);

   addRules(r);


   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method Action enq(LUInt#(max_in) count, Vector#(max_in, t) data) if (cfg.unguarded || (rDataCount.value() < fromInteger(valueOf(size))));
      rwEnqCount.wset(cExtend(count));
      rwEnqData.wset(pack(data));
   endmethod

   method Vector#(max_out, t) first() if (cfg.unguarded || (rDataCount.value() > 0));
      Vector#(max, t) v = newVector;
      for(Integer i = 0; i < valueOf(max); i = i + 1) begin
	 if (vfStorage[i].notEmpty()) v[i] = vfStorage[i].first();
	 else                         v[i] = ?;
      end
      return take(rotateRBy(v, cExtend(rReadIndex)));
   endmethod

   method Action deq(LUInt#(max_out) count) if (cfg.unguarded || (rDataCount.value() > 0));
      LUInt#(size) szcount = cExtend(count);
      rwDeqCount.wset(szcount);
   endmethod

   method Bool enqReady();
      return rDataCount.value < fromInteger(valueOf(size));
   endmethod

   method Bool enqReadyN(LUInt#(max_in) count);
      return (rDataCount.value() + cExtend(count)) <= fromInteger(valueOf(size));
   endmethod

   method Bool deqReady();
      return rDataCount.value() > 0;
   endmethod

   method Bool deqReadyN(LUInt#(max_out) count);
      return rDataCount.value() >= cExtend(count);
   endmethod

   method LUInt#(size) count();
      return cExtend(rDataCount.value());
   endmethod

   method Action clear();
      pwClear.send();
   endmethod
endmodule: mkMIMOBram

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of register based MIMO
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkMIMOReg#(MIMOConfiguration cfg)(MIMO#(max_in, max_out, size, t))
   provisos (  Bits#(t, st)               // object must have bit representation
	     , Add#(2, __a, size)         // must have at least 2 elements of storage
	     , Add#(__b, max_in, size)    // the max enqueued amount must be less than or equal to the full storage
	     , Add#(__c, max_out, size)   // the max dequeued amount must be less than or equal to the full storage
             , Mul#(st, size, total)      // total bits of storage
             , Mul#(st, max_in, intot)    // total bits to be enqueued
             , Mul#(st, max_out, outtot)  // total bits to be dequeued
             , Add#(__d, outtot, total)   // make sure the number of dequeue bits is not larger than the total storage
             );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Bit#(total))                rStorage            <- mkReg(0);
   Reg#(Bit#(total))                rStorageMask        <- mkReg(0);
   Reg#(LUInt#(size))               rDataCount          <- mkReg(0);
   Reg#(LUInt#(size))               rDataAvail          <- mkReg(fromInteger(valueOf(size)));

   RWire#(LUInt#(size))             rwDeqCount          <- mkRWire;
   RWire#(LUInt#(size))             rwEnqCount          <- mkRWire;
   RWire#(Bit#(intot))              rwEnqData           <- mkRWire;
   RWire#(Bit#(intot))              rwEnqMask           <- mkRWire;
   PulseWire                        pwClear             <- mkPulseWire;

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* fire_when_enabled, no_implicit_conditions *)
   rule update;
      LUInt#(size) nextDataCount = rDataCount;
      LUInt#(size) nextDataAvail = rDataAvail;
      Bit#(total)  nextStorage   = rStorage;
      Bit#(total)  nextMask      = rStorageMask;
      UInt#(32)    shift_amt     = 0;

      // Adjust the storage with dequeue data first
      LUInt#(size) deqCount = cExtend(fromMaybe(0, rwDeqCount.wget));
      shift_amt = cExtend(deqCount) * fromInteger(valueOf(st));
      nextStorage   = nextStorage >> shift_amt;
      nextMask      = nextMask    >> shift_amt;
      nextDataCount = nextDataCount - deqCount;
      nextDataAvail = nextDataAvail + deqCount;

      // Add Enqueue data next
      LUInt#(size) enqCount = cExtend(fromMaybe(0, rwEnqCount.wget));
      shift_amt = cExtend(nextDataCount) * fromInteger(valueOf(st));
      Bit#(total)  enqData  = cExtend(fromMaybe(0, rwEnqData.wget)) << shift_amt;
      Bit#(total)  enqMask  = cExtend(fromMaybe(0, rwEnqMask.wget)) << shift_amt;
      nextStorage   = (nextStorage & nextMask) | (enqData & enqMask);
      nextMask      = nextMask | enqMask;
      nextDataCount = nextDataCount + enqCount;
      nextDataAvail = nextDataAvail - enqCount;

      // Clear if needed (clearing overrides any enq/deq operation)
      if (pwClear) begin
         nextDataCount = 0;
         nextDataAvail = fromInteger(valueOf(size));
         nextStorage   = 0;
         nextMask      = 0;
      end

      // Apply updates to registers
      rStorage     <= nextStorage;
      rStorageMask <= nextMask;
      rDataCount   <= nextDataCount;
      rDataAvail   <= nextDataAvail;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method Action enq(LUInt#(max_in) count, Vector#(max_in, t) data) if (cfg.unguarded || (rDataCount < fromInteger(valueOf(size))));
      function Bit#(st) create_bitmask(Bit#(1) in) = (in == 1) ? '1 : '0;
      function Bit#(max_in) create_mask(LUInt#(max_in) i) = (1 << i)-1;

      LUInt#(size) szcount = cExtend(count);
      Vector#(max_in, Bit#(1)) mask = unpack(create_mask(count));
      Bit#(intot)  bitmask = pack(map(create_bitmask, mask));

      rwEnqCount.wset(szcount);
      rwEnqData.wset(pack(data));
      rwEnqMask.wset(bitmask);
   endmethod

   method Vector#(max_out, t) first() if (cfg.unguarded || (rDataCount > 0));
      Bit#(outtot) result = truncate(rStorage);
      return unpack(result);
   endmethod

   method Action deq(LUInt#(max_out) count) if (cfg.unguarded || (rDataCount > 0));
      LUInt#(size) szcount = cExtend(count);
      rwDeqCount.wset(szcount);
   endmethod

   method Bool enqReady();
      return rDataAvail > 0;
   endmethod

   method Bool enqReadyN(LUInt#(max_in) count);
      return rDataAvail >= cExtend(count);
   endmethod

   method Bool deqReady();
      return rDataCount > 0;
   endmethod

   method Bool deqReadyN(LUInt#(max_out) count);
      return rDataCount >= cExtend(count);
   endmethod

   method LUInt#(size) count();
      return cExtend(rDataCount);
   endmethod

   method Action clear();
      pwClear.send();
   endmethod
endmodule: mkMIMOReg

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of MIMO
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkMIMO#(MIMOConfiguration cfg)(MIMO#(max_in, max_out, size, t))
   provisos (  Bits#(t, st)               // object must have bit representation
	     , Add#(1, __e, st)           // object must be at least 1 bit in size
	     , Add#(2, __a, size)         // must have at least 2 elements of storage
	     , Add#(__b, max_in, size)    // the max enqueued amount must be less than or equal to the full storage
	     , Add#(__c, max_out, size)   // the max dequeued amount must be less than or equal to the full storage
             , Mul#(st, size, total)      // total bits of storage
             , Mul#(st, max_in, intot)    // total bits to be enqueued
             , Mul#(st, max_out, outtot)  // total bits to be dequeued
             , Add#(__d, outtot, total)   // make sure the number of dequeue bits is not larger than the total storage
             );

   MIMO#(max_in, max_out, size, t) ifc;

   if (cfg.bram_based) begin
      (* hide *)
      ifc <- mkMIMOBram(cfg);
   end
   else begin
      (* hide *)
      ifc <- mkMIMOReg(cfg);
   end
   return ifc;
endmodule


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of Vector based MIMO
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkMIMOV(MIMO#(max_in, max_out, size, t))
   provisos (  Bits#(t, st)               // object must have bit representation
	     , DefaultValue#(t)           // a default value must be defined for the object
	     , Add#(2, __a, size)         // must have at least 2 elements of storage
	     , Add#(__b, max_in, size)    // the max enqueued amount must be less than or equal to the full storage
	     , Add#(__c, max_out, size)   // the max dequeued amount must be less than or equal to the full storage
	     );

   // Some constants
   Integer iSize = valueOf(size);
   Integer dSize = valueOf(st);
   Vector#(size,t) nullVector = replicate(defaultValue);
   Vector#(size,Bool) enqMask = replicate(False);
   Vector#(max_in,Bool) enqMask2 = replicate(True);

   Vector#(size,Bit#(st)) enqMaskB = replicate('0);
   Vector#(max_in,Bit#(st)) enqMaskB2 = replicate('1);

   //   function t updateFunc (Bool sel , t a, t b) = sel ? a : b;

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(Vector#(size, t))                    rvData              <- mkReg(replicate(defaultValue));
   Reg#(LUInt#(size))                        rDataCount          <- mkReg(0);

   RWire#(LUInt#(size))                      rwDeqCount          <- mkRWire;
   RWire#(LUInt#(size))                      rwEnqCount          <- mkRWire;
   RWire#(Vector#(max_in, t))                rwvEnqData          <- mkRWire;
   PulseWire                                 pwClear             <- mkPulseWire;

   LUInt#(size) deqCount = cExtend(fromMaybe(0, rwDeqCount.wget));
   LUInt#(size) enqCount = cExtend(fromMaybe(0, rwEnqCount.wget));
   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* fire_when_enabled, no_implicit_conditions *)
   rule update (enqCount != 0 || deqCount != 0 || pwClear) ;
      Vector#(size, t)    nextData  = rvData;
      LUInt#(size)        nextCount = rDataCount;

      // Dequeue data before enqueueing
      // nextData = shiftOutFrom0(defaultValue, nextData, deqCount);
      nextData = unpack (pack(nextData) >> UInt#(32) ' (cExtend(deqCount) * fromInteger(dSize)));
      nextCount = rDataCount - deqCount;

      // Enqueue Data
      if (rwvEnqData.wget matches tagged Valid .enqData) begin
         UInt#(32) shiftAmt = fromInteger(dSize) * (fromInteger(iSize) - cExtend(nextCount));
         Vector#(TAdd#(size,max_in), t) datain = append( nullVector,enqData);
         //Vector#(size, t) dataShift  = take(shiftOutFrom0(defaultValue, datain, fromInteger(iSize) - cExtend(nextCount) ));
         Vector#(TAdd#(size,max_in), t) ds1 = unpack ( pack(datain) >> shiftAmt );
         Vector#(size, t) dataShift  = take (ds1);

         // Vector#(TAdd#(size,max_in), Bool) mask = append( enqMask, enqMask2);
         // Vector#(size, Bool) maskShift  = take (shiftOutFrom0( False, mask, fromInteger(iSize) - cExtend(nextCount) ));

         Vector#(TAdd#(size,max_in),Bit#(st)) enqMask1 = append(enqMaskB, enqMaskB2);
         Vector#(TAdd#(size,max_in),Bit#(st)) enqMask2 = unpack (pack(enqMask1) >> shiftAmt);
         Vector#(size, Bit#(st)) bitMask = take (enqMask2);

         // State updates
         //nextData =  zipWith3 ( updateFunc,maskShift, dataShift, nextData);
         nextData = unpack (pack(bitMask) & pack(dataShift) | (~pack(bitMask)) & pack(nextData));
         nextCount = nextCount + enqCount;
      end

      // clear if asked
      if (pwClear) begin
	 nextData = replicate(defaultValue);
	 nextCount = 0;
      end
      // update the registers!
      rvData      <= nextData;
      rDataCount  <= nextCount;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method    Action                      enq(LUInt#(max_in) count, Vector#(max_in, t) data) if (rDataCount < fromInteger(iSize));
      LUInt#(size) szcount = cExtend(count);
      rwEnqCount.wset(szcount);
      rwvEnqData.wset(data);
   endmethod

   method    Vector#(max_out, t)         first() if (rDataCount > 0);
      return takeAt(0, rvData);
   endmethod

   method    Action                      deq(LUInt#(max_out) count) if (rDataCount > 0);
      LUInt#(size) szcount = cExtend(count);
      rwDeqCount.wset(szcount);
   endmethod

   method    Bool                        enqReady();
      return rDataCount < fromInteger(iSize);
   endmethod

   method    Bool                        enqReadyN(LUInt#(max_in) count);
      return rDataCount <= (fromInteger(iSize) - cExtend(count));
   endmethod

   method    Bool                        deqReady();
      return rDataCount > 0;
   endmethod

   method    Bool                        deqReadyN(LUInt#(max_out) count);
      return rDataCount >= cExtend(count);
   endmethod

   method    LUInt#(size)                count();
      return cExtend(rDataCount);
   endmethod

   method    Action                      clear();
      pwClear.send;
   endmethod
endmodule


// (*synthesize*)
// module mkMIMOXX (MIMO#(4, 1600, 200, Bit#(8)));
//    let _i <- mkMIMOV();
//    return _i;
// endmodule


endpackage: MIMO

