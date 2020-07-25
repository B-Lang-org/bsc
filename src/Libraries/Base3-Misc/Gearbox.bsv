////////////////////////////////////////////////////////////////////////////////
//  Filename      : Gearbox.bsv
//  Description   : This file defines converters which are FIFO-like modules that
//                  convert N-wide data to/from 1-wide data at N-times the frequency.
//                  They are intended to be used with aligned clocks in the N:1 or
//                  1:N ratio.
//                  These modules are written in pure BSV using a style that utilizes
//                  only mkNullCrossingReg to cross registered values between clock
//                  domains.  Restricting the form of clock crossings is important to
//                  ensure that the module preserves atomic semantics and is compatible
//                  with both Verilog and Bluesim backends.
////////////////////////////////////////////////////////////////////////////////
package Gearbox;

// Notes :
// - sReset and dReset should be asserted together, otherwise only half the unit
//   will be reset.

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Clocks            ::*;
import Vector            ::*;

////////////////////////////////////////////////////////////////////////////////
/// Exports
////////////////////////////////////////////////////////////////////////////////
export Gearbox(..);
export mkNto1Gearbox;
export mk1toNGearbox;

////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////
interface Gearbox#(numeric type in, numeric type out, type a);
   method    Action          enq(Vector#(in, a) din);
   method    Action          deq();
   method    Vector#(out, a) first();
   method    Bool            notFull();
   method    Bool            notEmpty();
endinterface

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of N:1 Gearbox
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkNto1Gearbox(Clock sClock, Reset sReset,
		     Clock dClock, Reset dReset,
		     Gearbox#(in, out, a) ifc)
   provisos(
	    Bits#(a, a_sz),
	    Add#(out, 0, 1),
	    Add#(out, z, in)
	    );

   // 2xN elements of data storage are provided.
   // They are grouped into 2 blocks of N elements each.
   // Each block is writable in the source (slow) domain
   // and readable in the destination (fast) domain.
   CrossingReg#(Vector#(in, a))              block0              <- mkNullCrossingReg(dClock, unpack(0), clocked_by sClock, reset_by sReset);
   CrossingReg#(Vector#(in, a))              block1              <- mkNullCrossingReg(dClock, unpack(0), clocked_by sClock, reset_by sReset);

   // The source alternates which block it writes into.
   Reg#(UInt#(1))                            write_block         <- mkReg(0, clocked_by sClock, reset_by sReset);
   Reg#(UInt#(1))                            read_block          <- mkReg(0, clocked_by dClock, reset_by dReset);

   // The status of each block is distributed across the source
   // and destination domains.  There is a bit in the source
   // domain for each block and a bit in the destination domain
   // for each of the block's N elements.  The status of a
   // block is encoded in these bits:
   //
   //
   //   Block   Lo Elem   Hi Elem  |  Status
   //   ---------------------------+-----------
   //     0        0         0     |  Empty
   //     1        0         0     |  Full
   //     1        1         0     |  Half-Full
   //     1        1         1     |  Empty
   //     0        1         1     |  Full
   //     0        0         1     |  Half-Full
   //   ---------------------------+-----------
   //     0        1         0     |  ILLEGAL
   //     1        0         1     |  ILLEGAL
   //
   // The encoding allows an empty block to be made full
   // by toggling the block bit on the source side, and
   // to return to the empty state in N steps by toggling
   // the element bits on the destination side.

   CrossingReg#(Bool)                        block0_status       <- mkNullCrossingReg(dClock, False, clocked_by sClock, reset_by sReset);
   Vector#(in, CrossingReg#(Bool))           elem0_status        <- replicateM(mkNullCrossingReg(sClock, False, clocked_by dClock, reset_by dReset));

   CrossingReg#(Bool)                        block1_status       <- mkNullCrossingReg(dClock, False, clocked_by sClock, reset_by sReset);
   Vector#(in, CrossingReg#(Bool))           elem1_status        <- replicateM(mkNullCrossingReg(sClock, False, clocked_by dClock, reset_by dReset));

   function Bool isEqualToBlock0Status(Bool elemStatus);
      return (elemStatus == block0_status);
   endfunction

   function Bool isEqualToBlock1Status(Bool elemStatus);
      return (elemStatus == block1_status);
   endfunction

   function Bool isEqualToBlock0CStatus(Bool elemStatus);
      return (elemStatus == block0_status.crossed());
   endfunction

   function Bool isEqualToBlock1CStatus(Bool elemStatus);
      return (elemStatus == block1_status.crossed());
   endfunction

   // The encoding bits can be read in both domains, allowing
   // both the source and destination sides to agree on
   // the state of the blocks.
   Bool sBlock0_empty = unpack(&pack(map(isEqualToBlock0Status, readVCCReg(elem0_status))));
   Bool sBlock1_empty = unpack(&pack(map(isEqualToBlock1Status, readVCCReg(elem1_status))));

   Bool dBlock0_empty = unpack(&pack(map(isEqualToBlock0CStatus, readVCReg(elem0_status))));
   Bool dBlock1_empty = unpack(&pack(map(isEqualToBlock1CStatus, readVCReg(elem1_status))));

   // We can enqueue whenever the target write block is empty
   Bool ok_to_enq     = ((write_block == 0) && sBlock0_empty) ||
                        ((write_block == 1) && sBlock1_empty);

   // We can dequeue whenever the target read block is not empty
   Bool ok_to_deq     = ((read_block == 0) && !dBlock0_empty) ||
                        ((read_block == 1) && !dBlock1_empty);

   // Combine the sReset and dReset into identical resets in both domains.
   // These are used to disable both sides of the interface whenever
   // either domain is in reset.
   Reset                                     sCrosseddReset      <- mkAsyncReset(0, dReset, sClock);
   Reset                                     dCrossedsReset      <- mkAsyncReset(0, sReset, dClock);
   Reset                                     sCombinedReset      <- mkResetEither(sReset, sCrosseddReset, clocked_by sClock);
   Reset                                     dCombinedReset      <- mkResetEither(dReset, dCrossedsReset, clocked_by dClock);

   ReadOnly#(Bool)                           sInReset_pre        <- isResetAsserted(clocked_by sClock, reset_by sCombinedReset);
   ReadOnly#(Bool)                           dInReset_pre        <- isResetAsserted(clocked_by dClock, reset_by dCombinedReset);

   // Use pulsewires with noReset to eliminate compiler warnings when
   // the combined resets are used

   Wire#(Bool) sInReset <- mkBypassWire(clocked_by sClock, reset_by noReset);

   (* fire_when_enabled, no_implicit_conditions *)
   rule launder_sInReset;
      sInReset <= sInReset_pre;
   endrule

   Wire#(Bool) dInReset <- mkBypassWire(clocked_by dClock, reset_by noReset);

   (* fire_when_enabled, no_implicit_conditions *)
   rule launder_dInReset;
      dInReset <= dInReset_pre;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   // Enqueue in source (slow) domain by updating the target
   // write block and flipping its status bit, moving it
   // from Empty to Full.
   method Action enq(Vector#(in, a) din) if (ok_to_enq && !sInReset);
      write_block <= write_block ^ 1;
      if (write_block == 0) begin
	 block0        <= din;
	 block0_status <= !block0_status;
      end
      else begin
	 block1        <= din;
	 block1_status <= !block1_status;
      end
   endmethod

   // Dequeue in destination (fast) domain by flipping an
   // element status bit, moving the block from Full to
   // Half-Full, or from Half-Full to Half-Full, or from
   // Half-Full to Empty.
   method Action deq() if (ok_to_deq && !dInReset);
      if (read_block == 0) begin
	 let v = readVCReg(elem0_status);
	 v = shiftInAt0(v, block0_status.crossed);
	 writeVCReg(elem0_status, v);
	 if (last(v) == block0_status.crossed) begin
	    read_block <= 1;
	 end
      end
      else begin
	 let v = readVCReg(elem1_status);
	 v = shiftInAt0(v, block1_status.crossed);
	 writeVCReg(elem1_status, v);
	 if (last(v) == block1_status.crossed) begin
	    read_block <= 0;
	 end
      end
   endmethod

   // Retrieve the next value in the destination (fast) domain
   // by selecting the correct portion of the current read block.
   method Vector#(out, a) first() if (ok_to_deq && !dInReset);
      if (read_block == 0) begin
	 let v = readVCReg(elem0_status);
	 Bool found = False;
	 Vector#(out, a) result = ?;
	 for(Integer i = 0; i < valueof(in); i = i + 1) begin
	    if (v[i] != block0_status.crossed && !found) begin
	       result[0] = block0.crossed[i];
	       found  = True;
	    end
	 end
	 return result;
      end
      else begin
	 let v = readVCReg(elem1_status);
	 Bool found = False;
	 Vector#(out, a) result = ?;
	 for(Integer i = 0; i < valueof(in); i = i + 1) begin
	    if (v[i] != block1_status.crossed && !found) begin
	       result[0] = block1.crossed[i];
	       found  = True;
	    end
	 end
	 return result;
      end
   endmethod

   // Retrieve the notEmpty status in the destination (fast) domain.
   method Bool notEmpty();
      return ok_to_deq;
   endmethod

   // Retrieve the notFull status in the source (slow) domain.
   method Bool notFull();
      return ok_to_enq;
   endmethod

endmodule: mkNto1Gearbox

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of 1:N Gearbox
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mk1toNGearbox(Clock sClock, Reset sReset,
		     Clock dClock, Reset dReset,
		     Gearbox#(in, out, a) ifc)
   provisos(
	    Bits#(a, a_sz),
	    Add#(in, 0, 1),
	    Add#(in, z, out),
	    Mul#(2, out, elements),
	    Add#(1, w, elements),
	    Add#(out, x, elements)
	    );

   // 2xN elements of data storage are provided.
   // They are grouped into 2 blocks of N elements each.
   // Each block is writable in the source (fast) domain
   // and readable in the destination (slow) domain.
   Vector#(elements, CrossingReg#(a))        elem                <- replicateM(mkNullCrossingReg(dClock, unpack(0), clocked_by sClock, reset_by sReset));

   // The source alternates which block it writes into.
   Reg#(UInt#(1))                            write_block         <- mkReg(0, clocked_by sClock, reset_by sReset);

   // The destination alternates which block it reads from.
   Reg#(UInt#(1))                            read_block          <- mkReg(0, clocked_by dClock, reset_by dReset);

   // The status of each block is distributed across the source
   // and destination domains.  There is a bit in the source
   // domain for each element and a bit in the destination
   // domain for each block.  The status of a block is encoded
   // in these three bits:
   //
   //   Lo Elem   Hi Elem   Block  |  Status
   //   ---------------------------+-----------
   //      0         0        0    |  Empty
   //      1         0        0    |  Half-full
   //      1         1        0    |  Full
   //      1         1        1    |  Empty
   //      0         1        1    |  Half-full
   //      0         0        1    |  Full
   //   ---------------------------+-----------
   //      0         1        0    |  ILLEGAL
   //      1         0        1    |  ILLEGAL
   //
   // The encoding allows an empty block to be made half-full
   // and then full by toggling two bits on the source side,
   // and to return to the empty state in one step by toggling
   // the block bit on the destination side.

   CrossingReg#(Bool)                        block0_status       <- mkNullCrossingReg(sClock, False, clocked_by dClock, reset_by dReset);
   Vector#(out, CrossingReg#(Bool))          elem0_status        <- replicateM(mkNullCrossingReg(dClock, False, clocked_by sClock, reset_by sReset));

   CrossingReg#(Bool)                        block1_status       <- mkNullCrossingReg(sClock, False, clocked_by dClock, reset_by dReset);
   Vector#(out, CrossingReg#(Bool))          elem1_status        <- replicateM(mkNullCrossingReg(dClock, False, clocked_by sClock, reset_by sReset));

   function Bool isNotEqualToBlock0Status(Bool elemStatus);
      return (elemStatus != block0_status);
   endfunction

   function Bool isNotEqualToBlock1Status(Bool elemStatus);
      return (elemStatus != block1_status);
   endfunction

   function Bool isNotEqualToBlock0CStatus(Bool elemStatus);
      return (elemStatus != block0_status.crossed());
   endfunction

   function Bool isNotEqualToBlock1CStatus(Bool elemStatus);
      return (elemStatus != block1_status.crossed());
   endfunction

   // The encoding bits can be read in both domains, allowing
   // both the source and destination sides to agree on
   // the state of the blocks.

   Bool sBlock0_full = unpack(&pack(map(isNotEqualToBlock0CStatus, readVCReg(elem0_status))));
   Bool sBlock1_full = unpack(&pack(map(isNotEqualToBlock1CStatus, readVCReg(elem1_status))));

   Bool dBlock0_full = unpack(&pack(map(isNotEqualToBlock0Status, readVCCReg(elem0_status))));
   Bool dBlock1_full = unpack(&pack(map(isNotEqualToBlock1Status, readVCCReg(elem1_status))));

   // We can enqueue whenever the target write block is not full
   Bool ok_to_enq    = ((write_block == 0) && !sBlock0_full) ||
                       ((write_block == 1) && !sBlock1_full);

   Bool ok_to_deq    = ((read_block == 0) && dBlock0_full) ||
		       ((read_block == 1) && dBlock1_full);

   // Combine the sReset and dReset into identical resets in both domains.
   // These are used to disable both sides of the interface whenever either
   // domain is in reset.
   Reset                                     sCrosseddReset      <- mkAsyncReset(0, dReset, sClock);
   Reset                                     dCrossedsReset      <- mkAsyncReset(0, sReset, dClock);
   Reset                                     sCombinedReset      <- mkResetEither(sReset, sCrosseddReset, clocked_by sClock);
   Reset                                     dCombinedReset      <- mkResetEither(dReset, dCrossedsReset, clocked_by dClock);

   ReadOnly#(Bool)                           sInReset_pre        <- isResetAsserted(clocked_by sClock, reset_by sCombinedReset);
   ReadOnly#(Bool)                           dInReset_pre        <- isResetAsserted(clocked_by dClock, reset_by dCombinedReset);

   // Use pulsewires with noReset to eliminate compiler warnings when
   // the combined resets are used

   Wire#(Bool) sInReset <- mkBypassWire(clocked_by sClock, reset_by noReset);

   (* fire_when_enabled, no_implicit_conditions *)
   rule launder_sInReset;
      sInReset <= sInReset_pre;
   endrule

   Wire#(Bool) dInReset <- mkBypassWire(clocked_by dClock, reset_by noReset);

   (* fire_when_enabled, no_implicit_conditions *)
   rule launder_dInReset;
      dInReset <= dInReset_pre;
   endrule

   // Wires used to signal enq and deq

   PulseWire pwEnqueue <- mkPulseWire(clocked_by sClock, reset_by sReset);
   PulseWire pwDequeue <- mkPulseWire(clocked_by dClock, reset_by dReset);

   // Enqueue in source (fast) domain by updating the target
   // write element and flipping its status bit, moving the block
   // from Empty to Half-Full, Half-Full to Half-Full, and Half-Full
   // to Full.
   method Action enq(Vector#(in, a) din) if (ok_to_enq && !sInReset);
      pwEnqueue.send;
      if (write_block == 0) begin
	 let v = readVCReg(elem0_status);
	 Vector#(elements, a) w = readVCReg(elem);
	 Bool found = False;
	 for(Integer i = 0; i < valueof(out); i = i + 1) begin
	    if (v[i] == block0_status.crossed && !found) begin
	       w[i] = head(din);
	       found = True;
	    end
	 end
	 v = shiftInAt0(v, !block0_status.crossed);
	 writeVCReg(elem0_status, v);
	 writeVCReg(elem, w);
	 if (last(v) != block0_status.crossed) begin
	    write_block <= 1;
	 end
      end
      else begin
	 let v = readVCReg(elem1_status);
	 Vector#(elements, a) w = readVCReg(elem);
	 Bool found = False;
	 for(Integer i = valueof(out); i < valueof(elements); i = i + 1) begin
	    if (v[i-valueof(out)] == block1_status.crossed && !found) begin
	       w[i] = head(din);
	       found = True;
	    end
	 end
	 v = shiftInAt0(v, !block1_status.crossed);
	 writeVCReg(elem1_status, v);
	 writeVCReg(elem, w);
	 if (last(v) != block1_status.crossed) begin
	    write_block <= 0;
	 end
      end
   endmethod

   // Dequeue in destination (slow) domain by flipping the block
   // status bit, moving the block from Full to Empty.
   method Action deq() if (ok_to_deq && !dInReset);
      pwDequeue.send;
      read_block <= read_block ^ 1;
      if (read_block == 0) begin
	 block0_status <= !block0_status;
      end
      else begin
	 block1_status <= !block1_status;
      end
   endmethod

   // Retrieve the next value in the destination (slow) domain
   // by combining both elements of the current read block.
   method Vector#(out, a) first() if (ok_to_deq && !dInReset);
      Vector#(out, a) v = ?;
      if (read_block == 0) begin
	 v = takeAt(0, readVCCReg(elem));
      end
      else begin
	 v = takeAt(valueof(out), readVCCReg(elem));
      end
      return v;
   endmethod

   // Retrieve the notEmpty status in the destination (fast) domain.
   method Bool notEmpty();
      return ok_to_deq;
   endmethod

   // Retrieve the notFull status in the source (slow) domain.
   method Bool notFull();
      return ok_to_enq;
   endmethod

endmodule: mk1toNGearbox

////////////////////////////////////////////////////////////////////////////////
/// Handy Conversion Functions
////////////////////////////////////////////////////////////////////////////////
function b readCReg(CrossingReg#(b) x);
   return x._read;
endfunction

function b readCCReg(CrossingReg#(b) x);
   return x.crossed;
endfunction

function Action writeCReg(CrossingReg#(b) x, b in);
   return (action
	      x._write(in);
	   endaction);
endfunction

function Vector#(n, b) readVCReg(Vector#(n, CrossingReg#(b)) x) provisos(Add#(1, x2, n));
   return map(readCReg, x);
endfunction

function Vector#(n, b) readVCCReg(Vector#(n, CrossingReg#(b)) x) provisos(Add#(1, x2, n));
   return map(readCCReg, x);
endfunction

function Action writeVCReg(Vector#(n, CrossingReg#(b)) rs, Vector#(n, b) ds);
   return (action
	      joinActions(zipWith(writeCReg, rs, ds));
	   endaction);
endfunction
			
endpackage: Gearbox
