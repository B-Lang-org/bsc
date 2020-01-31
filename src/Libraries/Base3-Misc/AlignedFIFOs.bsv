package AlignedFIFOs;

// The AlignedFIFOs package contains a parameterized FIFO module
// intended for creating synchronizing FIFOs between clock domains
// with aligned edges.  Either every edge in the source domain implies
// the existence of a simultaneous edge in the destination domain (a
// slow-to-fast crossing), or every edge in the destination domain
// implies the existence of a simultaneous edge in the source domain
// (a fast-to-slow crossing).
//
// The FIFO is parameterized on the type of store used to hold the
// FIFO data, which is itself parameterized on the index type, value
// type and read latency.  Modules to construct stores based on a
// single register, a vector of registers and a BRAM are provided, and
// the user can supply their own store implementation as well.
//
// The FIFO allows the user to control whether or not outputs are held
// stable during the full slow clock cycle or allowed to transition
// mid-cycle.  Holding the outputs stable is the safest option but it
// slightly increases the minimum latency through the FIFO.
//
// A primary design goal of this FIFO is to provide an efficient
// and flexible family of synchronizing FIFOs between aligned clock
// domains which are written in BSV and are fully compatible with
// Bluesim.  These FIFOs (particularly ones using vectors of registers)
// may not be the best choice for ASIC synthesis due to the muxing
// to select the head value in the first() method.

import Clocks::*;
import Vector::*;
import BRAMCore::*;
import GetPut::*;

// Abstraction of indexed storage, with write and read in separate
// clock domains.  Type parameters are:
//   i - index type
//   a - value type
//   n - read latency (should be 0 or 1)
// When read latency is 0, prefetch is not used and read method index
// argument determines the returned value.  When latency is 1,
// prefetch must be used, the read method index argument is ignored,
// and the read method returns the value at the previously fetched
// index.
interface Store#(type i, type a, numeric type n);
   method Action write(i idx, a value);
   method Action prefetch(i idx);
   method a read(i idx);
endinterface: Store

// Make a register which can be read and written in
// different clock domains, with no safety checks.

(* always_ready *)
interface RawReg#(numeric type n);
   method Action write(Bit#(n) x);
   method Bit#(n) read();
endinterface: RawReg

import "BVI" RegUN =
   module vMkRegU(Clock dClock, RawReg#(n) ifc);
      default_clock sclk(CLK);
      no_reset;
      input_clock dclk () = dClock;
      parameter width = valueOf(n);
      method write(D_IN) enable(EN) clocked_by(sclk) reset_by(no_reset);
      method Q_OUT read() clocked_by(dclk) reset_by(no_reset);
      schedule read CF read;
      schedule write C write;
   endmodule: vMkRegU

// Implementation of a single-element store

module mkRegStore(Clock sClock, Clock dClock, Store#(UInt#(0),a,0) ifc)
   provisos(Bits#(a,a_sz));

   RawReg#(a_sz) _r <- vMkRegU(dClock, clocked_by sClock);

   method Action write(i idx, a value);
      _r.write(pack(value));
   endmethod

   method Action prefetch(i idx);
      $display("ERROR: Do not prefetch a RegStore (read latency is 0)!");
   endmethod

   method a read(i idx);
      return unpack(_r.read());
   endmethod

endmodule

// Implementation of a vector-of-registers store

module mkRegVectorStore(Clock sClock, Clock dClock, Store#(UInt#(w),a,0) ifc)
   provisos( Bits#(a,a_sz) );

   Vector#(TExp#(w),RawReg#(a_sz)) _v <- replicateM(vMkRegU(dClock, clocked_by sClock));

   method Action write(UInt#(w) idx, a value);
      _v[idx].write(pack(value));
   endmethod

   method Action prefetch(UInt#(w) idx);
      $display("ERROR: Do not prefetch a RegVectorStore (read latency is 0)!");
   endmethod

   method a read(UInt#(w) idx);
      return unpack(_v[idx].read());
   endmethod

endmodule

// Implementations of a BRAM-based store

module mkBRAMStore2W1R(Clock sClock, Reset sReset, Clock dClock, Reset dReset, Store#(i,a,1) ifc)
   provisos( Bits#(a,a_sz), Bits#(i,w), Eq#(i) );

   // this model assumes the read clock is a Nx divided version
   // of the write clock, so it requires a 2-deep write bypass
   // buffer
   Integer memSize = 2 ** valueOf( w );
   BRAM_DUAL_PORT#(i,a) bram  <- mkSyncBRAMCore2 ( memSize, False, sClock, noReset, dClock, noReset);

   Reg#(Bool) prefetch_ok     <- mkReg(False, clocked_by dClock, reset_by dReset);
   PulseWire  prefetch_called <- mkPulseWire(clocked_by dClock, reset_by dReset);
   CrossingReg#(i) rd_addr    <- mkNullCrossingRegU(sClock, clocked_by dClock);
   i crossed_rd_addr = rd_addr.crossed();

   Wire#(Tuple2#(i,a)) wr_record <- mkWire(clocked_by sClock, reset_by sReset);
   CrossingReg#(Maybe#(Tuple2#(i,a))) wr_buf0 <- mkNullCrossingReg(dClock, tagged Invalid, clocked_by sClock, reset_by sReset);
   Maybe#(Tuple2#(i,a)) crossed_wr_buf0 = wr_buf0.crossed();
   CrossingReg#(Maybe#(Tuple2#(i,a))) wr_buf1 <- mkNullCrossingReg(dClock, tagged Invalid, clocked_by sClock, reset_by sReset);
   Maybe#(Tuple2#(i,a)) crossed_wr_buf1 = wr_buf1.crossed();

   Bool two_deep;
   if (wr_buf0 matches tagged Valid {.wr_idx,.wr_value} &&& (wr_idx == crossed_rd_addr))
      two_deep = True;
   else if (wr_buf1 matches tagged Valid {.wr_idx,.wr_value} &&& (wr_idx == crossed_rd_addr))
      two_deep = False;
   else
      two_deep = True;

`ifdef ALIGNED_ORIG
   two_deep = True;
`endif

   rule record_prefetch;
      prefetch_ok <= prefetch_called;
   endrule

   rule record_write;
      if (two_deep) wr_buf1 <= wr_buf0;
      wr_buf0 <= tagged Valid wr_record;
   endrule

   method Action write(i idx, a value);
      wr_record <= tuple2(idx,value);
      bram.a.put(True, idx, value);
   endmethod

   method Action prefetch(i idx);
      rd_addr <= idx;
      bram.b.put(False, idx, ?);
      prefetch_called.send();
   endmethod

   method a read(i idx) if (prefetch_ok);
      a result;
      if (crossed_wr_buf0 matches tagged Valid {.wr_idx,.wr_value} &&& (wr_idx == rd_addr))
         result = wr_value;
      else if (crossed_wr_buf1 matches tagged Valid {.wr_idx,.wr_value} &&& (wr_idx == rd_addr))
         result = wr_value;
      else
         result = bram.b.read();
      return result;
   endmethod

endmodule


module mkBRAMStore1W2R(Clock sClock, Reset sReset, Clock dClock, Reset dReset, Store#(i,a,1) ifc)
   provisos( Bits#(a,a_sz), Bits#(i,w), Eq#(i) );

   // this model assumes the write clock is a Nx divided version
   // of the read clock, so it requires a 1-deep write bypass
   // buffer

   Integer memSize = 2 ** valueOf (w);
   BRAM_DUAL_PORT#(i,a) bram <- mkSyncBRAMCore2 ( memSize, False, sClock, noReset, dClock, noReset);

   Reg#(Bool) prefetch_ok     <- mkReg(False, clocked_by dClock, reset_by dReset);
   PulseWire  prefetch_called <- mkPulseWire(clocked_by dClock, reset_by dReset);
   Reg#(i)    rd_addr         <- mkRegU(clocked_by dClock);

   RWire#(Tuple2#(i,a)) wr_record <- mkRWire(clocked_by sClock, reset_by sReset);
   CrossingReg#(Maybe#(Tuple2#(i,a))) wr_buf0 <- mkNullCrossingReg(dClock, tagged Invalid, clocked_by sClock, reset_by sReset);
   Maybe#(Tuple2#(i,a)) crossed_wr_buf0 = wr_buf0.crossed();

   rule record_prefetch;
      prefetch_ok <= prefetch_called;
   endrule

   rule record_write;
      wr_buf0 <= wr_record.wget();
   endrule

   method Action write(i idx, a value);
      wr_record.wset(tuple2(idx,value));
      bram.a.put(True, idx, value);
   endmethod

   method Action prefetch(i idx);
      rd_addr <= idx;
      bram.b.put(False, idx, ?);
      prefetch_called.send();
   endmethod

   method a read(i idx) if (prefetch_ok);
      a result;
      if (crossed_wr_buf0 matches tagged Valid {.wr_idx,.wr_value} &&& (wr_idx == rd_addr))
         result = wr_value;
      else
         result = bram.b.read();
      return result;
   endmethod

endmodule


// Interface for synchronizing FIFO between clocks with
// aligned edges.
interface AlignedFIFO#(type a);
   method Action enq(a x);
   method a first();
   method Action deq();
   method Bool dNotFull();
   method Bool dNotEmpty();
   method Bool sNotFull();
   method Bool sNotEmpty();
   method Action dClear();
   method Action sClear();
endinterface: AlignedFIFO

// Make a synchronizing FIFO for aligned clocks, based on the
// given backing store.  The store is assumed to have 2^w slots
// addressed from 0 to (2^w)-1.  The store will be written in
// the source clock domain and read in the destination clock domain.
//
// The enq() and deq() methods will only be callable when the allow_enq
// and allow_deq inputs are high.  For a slow-to-fast crossing, use:
//   allow_enq = constant True and allow_deq = pre-edge signal
// For a fast-to-slow crossing, use:
//   allow_enq = pre-edge signal and allow_deq = constant True
// These settings ensure that the outputs in the slow clock
// domain are stable for the entire cycle.  Setting both inputs
// to constant True reduces the minimum latency through the FIFO,
// but allows outputs in the slow domain to transition mid-cycle.
// This is less safe and can interact badly with $displays in a
// Verilog simulation.
//
// It is not advisable to call both dClear and sClear simultaneously.

(* no_default_clock, no_default_reset *)
module mkUGAlignedFIFO( Bool ugenq
		      , Bool ugdeq
                      , Clock sClock
	 	      , Reset sReset
 		      , Clock dClock
		      , Reset dReset
		      , Store#(i,a,n) store
		      , Bool allow_enq
		      , Bool allow_deq
		      , AlignedFIFO#(a) ifc
		      )
   provisos( Bits#(a,sz_a), Bits#(i,w), Eq#(i), Arith#(i) );

   // Check the latency of the store
   Integer latency = valueOf(n);
   if ((latency < 0) || (latency > 1))
      errorM("mkUGAlignedFIFO expects a store with either 0 or 1 cycles of latency");

   // Combine the sReset and dReset into identical resets in both domains
   Reset sCrosseddReset <- mkAsyncReset(0,dReset,sClock);
   Reset dCrossedsReset <- mkAsyncReset(0,sReset,dClock);
   Reset sCombinedReset <- mkResetEither(sReset, sCrosseddReset, clocked_by sClock);
   Reset dCombinedReset <- mkResetEither(dReset, dCrossedsReset, clocked_by dClock);

   // Test when resets are asserted
   ReadOnly#(Bool) sInReset <- isResetAssertedDirect(clocked_by sClock, reset_by sCombinedReset);
   ReadOnly#(Bool) dInReset <- isResetAssertedDirect(clocked_by dClock, reset_by dCombinedReset);

   // Location of next deq slot (in dest. domain)
   CrossingReg#(i) head <- mkNullCrossingReg(sClock, 0, clocked_by dClock, reset_by dReset);

   // Location of next enq slot (in src. domain)
   CrossingReg#(i) tail <- mkNullCrossingReg(dClock, 0, clocked_by sClock, reset_by sReset);

   PulseWire enq_pw    <- mkPulseWire(clocked_by sClock, reset_by sReset);
   PulseWire deq_pw    <- mkPulseWire(clocked_by dClock, reset_by dReset);
   PulseWire sClear_pw <- mkPulseWire(clocked_by sClock, reset_by sReset);
   PulseWire dClear_pw <- mkPulseWire(clocked_by dClock, reset_by dReset);

   // We track the "wrap state" as the parity of the number of
   // times that a value has wrapped around to 0.  Since the tail
   // can never overtake the head, we only need one bit of each
   // to distinguish between the empty and full states
   // (when head == tail).
   CrossingReg#(Bool) head_wrapped <- mkNullCrossingReg(sClock, False, clocked_by dClock, reset_by dReset);
   CrossingReg#(Bool) tail_wrapped <- mkNullCrossingReg(dClock, False, clocked_by sClock, reset_by sReset);

   // Cross head and tail info into alternate domains.
   // This is designed so that we only cross registered values.
   i    sCrossedHead        = head.crossed();
   Bool sCrossedHeadWrapped = head_wrapped.crossed();
   i    dCrossedTail        = tail.crossed();
   Bool dCrossedTailWrapped = tail_wrapped.crossed();

   // Make empty/full info available in both domains.
   // The FIFO is empty when head == tail in the same
   // wrap state.  The FIFO is full when head == tail
   // in opposite wrap states.
   Bool dIsEmpty = (head == dCrossedTail) &&
                   (head_wrapped == dCrossedTailWrapped);
   Bool sIsEmpty = (sCrossedHead == tail) &&
                   (sCrossedHeadWrapped == tail_wrapped);
   Bool dIsFull  = (head == dCrossedTail) &&
                   (head_wrapped != dCrossedTailWrapped);
   Bool sIsFull  = (sCrossedHead == tail) &&
                   (sCrossedHeadWrapped != tail_wrapped);

   // Next head and tail values
   i next_tail;
   i next_head;
   if (valueOf(w) == 0)
   begin
      next_tail = tail;
      next_head = head;
   end
   else
   begin
      next_tail = tail + 1;
      next_head = head + 1;
   end

   // For a store with latency, we need to prefetch the value
   // to satisfy first() in the next cycle.  When the deq()
   // method is called we use the next head value, otherwise we
   // re-fetch the current head value.
   PulseWire deq_happened <- mkPulseWire(clocked_by dClock, reset_by dReset);
   if (latency != 0)
   begin
      Wire#(i) old_head <- mkBypassWire(clocked_by dClock, reset_by dReset);

      // In dClock domain (before deq())
      rule save_old_head;
	 old_head <= head;
      endrule

      // In dClock domain (after deq())
      rule do_fetch;
         store.prefetch(deq_happened ? (old_head + 1) : old_head);
      endrule
   end

   // When either side goes into reset, both sInReset and dInReset
   // will become True.  If only 1 reset is actually asserted, we have
   // a rule here which will force the other to assume its reset value
   // too.  This ensures that the FIFO resets correctly even if only
   // 1 of its 2 resets is asserted.

   // In sClock domain
   rule enq_update_tail (!sInReset && enq_pw && !sClear_pw);
      tail <= next_tail;
      if (next_tail == 0)
         tail_wrapped <= !tail_wrapped;
   endrule

   // In sClock domain
   rule sClear_update_tail (!sInReset && sClear_pw);
      tail <= sCrossedHead;
      tail_wrapped <= sCrossedHeadWrapped;
   endrule

   // In sClock domain
   rule reset_tail if (sInReset);
      tail <= 0;
      tail_wrapped <= False;
   endrule

   // In dClock domain
   rule deq_update_head (!dInReset && deq_pw && !dClear_pw);
      head <= next_head;
      if (next_head == 0)
	 head_wrapped <= !head_wrapped;
   endrule

   // In dClock domain
   rule dClear_update_head (!dInReset && dClear_pw);
      head <= dCrossedTail;
      head_wrapped <= dCrossedTailWrapped;
   endrule

   // In dClock domain
   rule reset_head if (dInReset);
      head <= 0;
      head_wrapped <= False;
   endrule

   // Interface methods

   // In sClock domain
   method Action enq(a x) if ((!sIsFull && !sInReset && allow_enq) || ugenq);
      enq_pw.send;
      store.write(tail,x);
   endmethod: enq

   // In dClock domain
   method a first if ((!dIsEmpty && !dInReset) || ugdeq);
      let result = ?;
      if (latency == 0)
	 result = store.read(head);
      else
	 result = store.read(?);
      return result;
   endmethod: first

   // In dClock domain
   method Action deq() if ((!dIsEmpty && !dInReset && allow_deq) || ugdeq);
      deq_pw.send;
      if (latency != 0)
	 deq_happened.send();
   endmethod: deq

   // Full/Empty methods
   method Bool dNotFull  = !dIsFull;
   method Bool dNotEmpty = !dIsEmpty;
   method Bool sNotFull  = !sIsFull;
   method Bool sNotEmpty = !sIsEmpty;

   // Clear FIFO from destination domain
   method Action dClear() if (allow_deq && !dInReset);
      dClear_pw.send;
   endmethod: dClear

   // Clear FIFO from source domain
   method Action sClear() if (allow_enq && !sInReset);
      sClear_pw.send;
   endmethod: sClear

endmodule: mkUGAlignedFIFO


(* no_default_clock, no_default_reset *)
module mkAlignedFIFO( Clock sClock
		    , Reset sReset
		    , Clock dClock
		    , Reset dReset
		    , Store#(i,a,n) store
		    , Bool allow_enq
		    , Bool allow_deq
		    , AlignedFIFO#(a) ifc
		    )
   provisos( Bits#(a,sz_a), Bits#(i,w), Eq#(i), Arith#(i) );

   // Check the latency of the store
   Integer latency = valueOf(n);
   if ((latency < 0) || (latency > 1))
      errorM("mkAlignedFIFO expects a store with either 0 or 1 cycles of latency");

   // Just use mkUGAlignedFIFO with both sides guarded
   let _fifo <- mkUGAlignedFIFO(False,False,sClock,sReset,dClock,dReset,store,allow_enq,allow_deq);

   return _fifo;

endmodule: mkAlignedFIFO

// Typeclass instances

instance ToGet#(AlignedFIFO#(t), t);
   function Get#(t) toGet(AlignedFIFO#(t) fifo);
      return (interface Get;
                 method ActionValue#(t) get();
                    fifo.deq();
                    return fifo.first();
                 endmethod
              endinterface);
   endfunction
endinstance

instance ToPut#(AlignedFIFO#(t), t);
   function Put#(t) toPut(AlignedFIFO#(t) fifo);
      return (interface Put;
                 method Action put(t val) = fifo.enq(val);
              endinterface);
   endfunction
endinstance

endpackage: AlignedFIFOs
