////////////////////////////////////////////////////////////////////////////////
//  Filename      : BRAMFIFO.bsv
//  Author        : Todd Snyder
//  Description   : BRAM based FIFO solution
////////////////////////////////////////////////////////////////////////////////

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Clocks            ::*;
import FIFO              ::*;
import FIFOF             ::*;
import BRAMCore          ::*;
import Gray              ::*;
import GrayCounter       ::*;
import ConfigReg         ::*;

////////////////////////////////////////////////////////////////////////////////
/// Exports
////////////////////////////////////////////////////////////////////////////////
export mkSizedBRAMFIFOF;
export mkSizedBRAMFIFO;
export mkSyncBRAMFIFO;
export mkSyncBRAMFIFOToCC;
export mkSyncBRAMFIFOFromCC;

////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////
interface IBRAMFIFOF#(numeric type log2depth, type t);
   interface FIFOF#(t) fifo;
endinterface: IBRAMFIFOF

interface ISyncBRAMFIFOFIfc#(numeric type log2depth, type t);
   interface SyncFIFOIfc#(t) fifo;
endinterface: ISyncBRAMFIFOFIfc

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of mkSizedBRAMFIFOF base module
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkSizedBRAMFIFOF#(Integer m)(FIFOF#(t))
   provisos(
	    Bits#(t, st),
	    Add#(1, z, st)
	    );

   let _i = ?;

   if      (m<2)      	  begin (* hide *) IBRAMFIFOF#(1, t)  _bramfifo1 <- mkSzBRAMFIFOF(m);  _i = _bramfifo1.fifo;  end
   else if (m<4)      	  begin (* hide *) IBRAMFIFOF#(2, t)  _bramfifo2 <- mkSzBRAMFIFOF(m);  _i = _bramfifo2.fifo;  end
   else if (m<8)      	  begin (* hide *) IBRAMFIFOF#(3, t)  _bramfifo3 <- mkSzBRAMFIFOF(m);  _i = _bramfifo3.fifo;  end
   else if (m<16)     	  begin (* hide *) IBRAMFIFOF#(4, t)  _bramfifo4 <- mkSzBRAMFIFOF(m);  _i = _bramfifo4.fifo;  end
   else if (m<32)     	  begin (* hide *) IBRAMFIFOF#(5, t)  _bramfifo5 <- mkSzBRAMFIFOF(m);  _i = _bramfifo5.fifo;  end
   else if (m<64)     	  begin (* hide *) IBRAMFIFOF#(6, t)  _bramfifo6 <- mkSzBRAMFIFOF(m);  _i = _bramfifo6.fifo;  end
   else if (m<128)    	  begin (* hide *) IBRAMFIFOF#(7, t)  _bramfifo7 <- mkSzBRAMFIFOF(m);  _i = _bramfifo7.fifo;  end
   else if (m<256)    	  begin (* hide *) IBRAMFIFOF#(8, t)  _bramfifo8 <- mkSzBRAMFIFOF(m);  _i = _bramfifo8.fifo;  end
   else if (m<512)    	  begin (* hide *) IBRAMFIFOF#(9, t)  _bramfifo9 <- mkSzBRAMFIFOF(m);  _i = _bramfifo9.fifo;  end
   else if (m<1024)   	  begin (* hide *) IBRAMFIFOF#(10, t) _bramfifo10 <- mkSzBRAMFIFOF(m); _i = _bramfifo10.fifo; end
   else if (m<2048)   	  begin (* hide *) IBRAMFIFOF#(11, t) _bramfifo11 <- mkSzBRAMFIFOF(m); _i = _bramfifo11.fifo; end
   else if (m<4096)   	  begin (* hide *) IBRAMFIFOF#(12, t) _bramfifo12 <- mkSzBRAMFIFOF(m); _i = _bramfifo12.fifo; end
   else if (m<8192)   	  begin (* hide *) IBRAMFIFOF#(13, t) _bramfifo13 <- mkSzBRAMFIFOF(m); _i = _bramfifo13.fifo; end
   else if (m<16384)  	  begin (* hide *) IBRAMFIFOF#(14, t) _bramfifo14 <- mkSzBRAMFIFOF(m); _i = _bramfifo14.fifo; end
   else if (m<32768)  	  begin (* hide *) IBRAMFIFOF#(15, t) _bramfifo15 <- mkSzBRAMFIFOF(m); _i = _bramfifo15.fifo; end
   else if (m<65536)  	  begin (* hide *) IBRAMFIFOF#(16, t) _bramfifo16 <- mkSzBRAMFIFOF(m); _i = _bramfifo16.fifo; end
   else if (m<101072) 	  begin (* hide *) IBRAMFIFOF#(17, t) _bramfifo17 <- mkSzBRAMFIFOF(m); _i = _bramfifo17.fifo; end
   else if (m<262144) 	  begin (* hide *) IBRAMFIFOF#(18, t) _bramfifo18 <- mkSzBRAMFIFOF(m); _i = _bramfifo18.fifo; end
   else if (m<524288) 	  begin (* hide *) IBRAMFIFOF#(19, t) _bramfifo19 <- mkSzBRAMFIFOF(m); _i = _bramfifo19.fifo; end
   else if (m<1048576) 	  begin (* hide *) IBRAMFIFOF#(20, t) _bramfifo20 <- mkSzBRAMFIFOF(m); _i = _bramfifo20.fifo; end
   else if (m<2097152) 	  begin (* hide *) IBRAMFIFOF#(21, t) _bramfifo21 <- mkSzBRAMFIFOF(m); _i = _bramfifo21.fifo; end
   else if (m<4194304) 	  begin (* hide *) IBRAMFIFOF#(22, t) _bramfifo22 <- mkSzBRAMFIFOF(m); _i = _bramfifo22.fifo; end
   else if (m<8388608) 	  begin (* hide *) IBRAMFIFOF#(23, t) _bramfifo23 <- mkSzBRAMFIFOF(m); _i = _bramfifo23.fifo; end
   else if (m<16777216)   begin (* hide *) IBRAMFIFOF#(24, t) _bramfifo24 <- mkSzBRAMFIFOF(m); _i = _bramfifo24.fifo; end
   else if (m<33554432)   begin (* hide *) IBRAMFIFOF#(25, t) _bramfifo25 <- mkSzBRAMFIFOF(m); _i = _bramfifo25.fifo; end
   else if (m<67108864)   begin (* hide *) IBRAMFIFOF#(26, t) _bramfifo26 <- mkSzBRAMFIFOF(m); _i = _bramfifo26.fifo; end
   else if (m<134217728)  begin (* hide *) IBRAMFIFOF#(27, t) _bramfifo27 <- mkSzBRAMFIFOF(m); _i = _bramfifo27.fifo; end
   else if (m<268435456)  begin (* hide *) IBRAMFIFOF#(28, t) _bramfifo28 <- mkSzBRAMFIFOF(m); _i = _bramfifo28.fifo; end
   else if (m<536870912)  begin (* hide *) IBRAMFIFOF#(29, t) _bramfifo29 <- mkSzBRAMFIFOF(m); _i = _bramfifo29.fifo; end
   else if (m<1073741824) begin (* hide *) IBRAMFIFOF#(30, t) _bramfifo30 <- mkSzBRAMFIFOF(m); _i = _bramfifo30.fifo; end
   else if (m<2147483648) begin (* hide *) IBRAMFIFOF#(31, t) _bramfifo31 <- mkSzBRAMFIFOF(m); _i = _bramfifo31.fifo; end
   else if (m<4294967296) begin (* hide *) IBRAMFIFOF#(32, t) _bramfifo32 <- mkSzBRAMFIFOF(m); _i = _bramfifo32.fifo; end

   return _i;
endmodule: mkSizedBRAMFIFOF

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of polymorphic version.
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkSzBRAMFIFOF#(Integer m)(IBRAMFIFOF#(l, t))
   provisos(
	    Bits#(t, st),
	    Add#(1, z, st),
	    Add#(1, l, d),
	    Add#(1, x, l)
	    );

   Clock                                     clk                 <- exposeCurrentClock;
   Reset                                     rstN                <- exposeCurrentReset;

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Integer memSize = 2 ** valueOf(l);
   BRAM_DUAL_PORT#(Bit#(l), t)               memory              <- mkBRAMCore2(memSize, False );

   Reg#(Bit#(d))                             rWrPtr              <- mkConfigReg(0);
   PulseWire                                 pwDequeue           <- mkPulseWire;
   PulseWire                                 pwEnqueue           <- mkPulseWire;
   PulseWire                                 pwClear             <- mkPulseWire;
   Wire#(t)                                  wDataIn             <- mkDWire(unpack(0));
   Reg#(Bit#(d))                             rRdPtr              <- mkConfigReg(0);
   Wire#(t)                                  wDataOut            <- mkWire;

   Reg#(Maybe#(Tuple2#(Bit#(d),t)))          rCache              <- mkReg(tagged Invalid);

   Bool empty = (rRdPtr == rWrPtr);
   Bool full  = ((rRdPtr + fromInteger(m)) == rWrPtr);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* fire_when_enabled, no_implicit_conditions, aggressive_implicit_conditions *)
   rule portA;
      if (pwClear) begin
	 rWrPtr <= 0;
      end
      else if (pwEnqueue) begin
	 memory.a.put(True, truncate(rWrPtr), wDataIn);
	 rCache <= tagged Valid tuple2(rWrPtr, wDataIn);  // cache last write
	 rWrPtr <= rWrPtr + 1;
      end
      else begin
	 memory.a.put(False, truncate(rWrPtr), ?);
      end
   endrule

   (* fire_when_enabled, no_implicit_conditions, aggressive_implicit_conditions *)
   rule portB;
      if (pwClear) begin
	 rRdPtr <= 0;
      end
      else if (pwDequeue) begin
	 memory.b.put(False, truncate(rRdPtr+1), ?);
	 rRdPtr <= rRdPtr + 1;
      end
      else begin
	 memory.b.put(False, truncate(rRdPtr), ?);
      end
   endrule

   (* fire_when_enabled, no_implicit_conditions *)
   rule portB_read_data;
      // if the read data is for the last address written, bypass the BRAM
      // and use the data stored in the cache.
      if (rCache matches tagged Valid {.addr, .data} &&& (addr == rRdPtr))
	 wDataOut <= data;
      else
	 wDataOut <= memory.b.read;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface FIFOF fifo;
      method Action enq(t sendData) if (!full);
	 pwEnqueue.send;
	 wDataIn <= sendData;
      endmethod

      method Action deq if (!empty);
	 pwDequeue.send;
      endmethod

      method t first if (!empty);
	 return wDataOut;
      endmethod

      method Bool notFull  = !full;
      method Bool notEmpty = !empty;

      method Action clear;
	 pwClear.send();
      endmethod
   endinterface: fifo

endmodule: mkSzBRAMFIFOF


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of mkSizedBRAMFIFO
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkSizedBRAMFIFO#(Integer n)(FIFO#(t))
   provisos(
	    Bits#(t, st),
	    Add#(1, z, st)
	    );

   (* hide *)
   let _m <- mkSizedBRAMFIFOF(n);
   return fifofToFifo(_m);
endmodule: mkSizedBRAMFIFO

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of mkSyncBRAMFIFO
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
(* no_default_clock, no_default_reset *)
module mkSyncBRAMFIFO#(Integer depth, Clock sClkIn, Reset sRstIn, Clock dClkIn, Reset dRstIn)(SyncFIFOIfc#(t))
   provisos(
	    Bits#(t, st),
   	    Add#(1, z, st)
	    );

   let _i = ?;


   if      (depth<2)          begin (* hide *) ISyncBRAMFIFOFIfc#(1, t)  _bramfifo1 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo1.fifo;  end
   else if (depth<4)          begin (* hide *) ISyncBRAMFIFOFIfc#(2, t)  _bramfifo2 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo2.fifo;  end
   else if (depth<8)          begin (* hide *) ISyncBRAMFIFOFIfc#(3, t)  _bramfifo3 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo3.fifo;  end
   else if (depth<16)         begin (* hide *) ISyncBRAMFIFOFIfc#(4, t)  _bramfifo4 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo4.fifo;  end
   else if (depth<32)         begin (* hide *) ISyncBRAMFIFOFIfc#(5, t)  _bramfifo5 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo5.fifo;  end
   else if (depth<64)         begin (* hide *) ISyncBRAMFIFOFIfc#(6, t)  _bramfifo6 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo6.fifo;  end
   else if (depth<128)        begin (* hide *) ISyncBRAMFIFOFIfc#(7, t)  _bramfifo7 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo7.fifo;  end
   else if (depth<256)        begin (* hide *) ISyncBRAMFIFOFIfc#(8, t)  _bramfifo8 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo8.fifo;  end
   else if (depth<512)        begin (* hide *) ISyncBRAMFIFOFIfc#(9, t)  _bramfifo9 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn);  _i = _bramfifo9.fifo;  end
   else if (depth<1024)       begin (* hide *) ISyncBRAMFIFOFIfc#(10, t) _bramfifo10 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo10.fifo; end
   else if (depth<2048)       begin (* hide *) ISyncBRAMFIFOFIfc#(11, t) _bramfifo11 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo11.fifo; end
   else if (depth<4096)       begin (* hide *) ISyncBRAMFIFOFIfc#(12, t) _bramfifo12 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo12.fifo; end
   else if (depth<8192)       begin (* hide *) ISyncBRAMFIFOFIfc#(13, t) _bramfifo13 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo13.fifo; end
   else if (depth<16384)      begin (* hide *) ISyncBRAMFIFOFIfc#(14, t) _bramfifo14 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo14.fifo; end
   else if (depth<32768)      begin (* hide *) ISyncBRAMFIFOFIfc#(15, t) _bramfifo15 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo15.fifo; end
   else if (depth<65536)      begin (* hide *) ISyncBRAMFIFOFIfc#(16, t) _bramfifo16 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo16.fifo; end
   else if (depth<101072)     begin (* hide *) ISyncBRAMFIFOFIfc#(17, t) _bramfifo17 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo17.fifo; end
   else if (depth<262144)     begin (* hide *) ISyncBRAMFIFOFIfc#(18, t) _bramfifo18 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo18.fifo; end
   else if (depth<524288)     begin (* hide *) ISyncBRAMFIFOFIfc#(19, t) _bramfifo19 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo19.fifo; end
   else if (depth<1048576)    begin (* hide *) ISyncBRAMFIFOFIfc#(20, t) _bramfifo20 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo20.fifo; end
   else if (depth<2097152)    begin (* hide *) ISyncBRAMFIFOFIfc#(21, t) _bramfifo21 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo21.fifo; end
   else if (depth<4194304)    begin (* hide *) ISyncBRAMFIFOFIfc#(22, t) _bramfifo22 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo22.fifo; end
   else if (depth<8388608)    begin (* hide *) ISyncBRAMFIFOFIfc#(23, t) _bramfifo23 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo23.fifo; end
   else if (depth<16777216)   begin (* hide *) ISyncBRAMFIFOFIfc#(24, t) _bramfifo24 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo24.fifo; end
   else if (depth<33554432)   begin (* hide *) ISyncBRAMFIFOFIfc#(25, t) _bramfifo25 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo25.fifo; end
   else if (depth<67108864)   begin (* hide *) ISyncBRAMFIFOFIfc#(26, t) _bramfifo26 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo26.fifo; end
   else if (depth<134217728)  begin (* hide *) ISyncBRAMFIFOFIfc#(27, t) _bramfifo27 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo27.fifo; end
   else if (depth<268435456)  begin (* hide *) ISyncBRAMFIFOFIfc#(28, t) _bramfifo28 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo28.fifo; end
   else if (depth<536870912)  begin (* hide *) ISyncBRAMFIFOFIfc#(29, t) _bramfifo29 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo29.fifo; end
   else if (depth<1073741824) begin (* hide *) ISyncBRAMFIFOFIfc#(30, t) _bramfifo30 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo30.fifo; end
   else if (depth<2147483648) begin (* hide *) ISyncBRAMFIFOFIfc#(31, t) _bramfifo31 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo31.fifo; end
   else if (depth<4294967296) begin (* hide *) ISyncBRAMFIFOFIfc#(32, t) _bramfifo32 <- mkSncBRAMFIFOF(depth, sClkIn, sRstIn, dClkIn, dRstIn); _i = _bramfifo32.fifo; end

   return _i;
endmodule: mkSyncBRAMFIFO

module mkSncBRAMFIFOF#(Integer depth, Clock sClkIn, Reset sRstIn, Clock dClkIn, Reset dRstIn)(ISyncBRAMFIFOFIfc#(l, t))
   provisos(
	    Bits#(t, st),
	    Add#(1, z, st),
	    Add#(1, l, d),
	    Add#(1, x, l)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Integer memSize = 2 ** valueOf(l);
   BRAM_DUAL_PORT#(Bit#(l), t)               memory              <- mkSyncBRAMCore2(memSize, False, sClkIn, sRstIn, dClkIn, dRstIn);

   GrayCounter#(d)                           rWrPtr              <- mkGrayCounter(unpack(0), dClkIn, dRstIn, clocked_by sClkIn, reset_by sRstIn);
   GrayCounter#(d)                           rRdPtr              <- mkGrayCounter(unpack(0), sClkIn, sRstIn, clocked_by dClkIn, reset_by dRstIn);
   PulseWire                                 pwDequeue           <- mkPulseWire(clocked_by dClkIn, reset_by dRstIn);
   PulseWire                                 pwEnqueue           <- mkPulseWire(clocked_by sClkIn, reset_by sRstIn);
   Wire#(t)                                  wDataIn             <- mkDWire(unpack(0), clocked_by sClkIn, reset_by sRstIn);
   Wire#(t)                                  wDataOut            <- mkWire(clocked_by dClkIn, reset_by dRstIn);

   Bool empty = rRdPtr.sReadGray == rWrPtr.dReadGray;
   Bool full  = rWrPtr.sReadGray == grayEncode(rRdPtr.dReadBin + fromInteger(depth));

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* fire_when_enabled, no_implicit_conditions *)
   rule portA;
      if (pwEnqueue) begin
	 memory.a.put(True, truncate(rWrPtr.sReadBin), wDataIn);
	 rWrPtr.incr;
      end
      else begin
	 memory.a.put(False, truncate(rWrPtr.sReadBin), ?);
      end
   endrule

   (* fire_when_enabled, no_implicit_conditions *)
   rule portB;
      if (pwDequeue) begin
	 memory.b.put(False, truncate(rRdPtr.sReadBin+1), ?);
	 rRdPtr.incr;
      end
      else begin
	 memory.b.put(False, truncate(rRdPtr.sReadBin), ?);
      end
   endrule

   (* fire_when_enabled, no_implicit_conditions *)
   rule portB_read_data;
      wDataOut <= memory.b.read;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface SyncFIFOIfc fifo;
      method Action enq(t sendData) if (!full);
	 pwEnqueue.send;
	 wDataIn <= sendData;
      endmethod

      method Action deq if (!empty);
	 pwDequeue.send;
      endmethod

      method t first if (!empty);
	 return wDataOut;
      endmethod

      method Bool notFull  = !full;
      method Bool notEmpty = !empty;

   endinterface: fifo

endmodule: mkSncBRAMFIFOF


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of mkSyncBRAMFIFOToCC
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkSyncBRAMFIFOToCC#(Integer depth, Clock sClkIn, Reset sRstIn)(SyncFIFOIfc#(t))
   provisos(
	    Bits#(t, st),
   	    Add#(1, z, st)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   (* hide *)
   let _m    <- mkSyncBRAMFIFO(depth, sClkIn, sRstIn, clk, rst);
   return _m;
endmodule: mkSyncBRAMFIFOToCC

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of mkSyncBRAMFIFOFromCC
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkSyncBRAMFIFOFromCC#(Integer depth, Clock dClkIn, Reset dRstIn)(SyncFIFOIfc#(t))
   provisos(
	    Bits#(t, st),
   	    Add#(1, z, st)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   (* hide *)
   let _m    <- mkSyncBRAMFIFO(depth, clk, rst, dClkIn, dRstIn);
   return _m;
endmodule: mkSyncBRAMFIFOFromCC
