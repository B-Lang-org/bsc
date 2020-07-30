package WBone;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import ZBus::*;
import List::*;
import Connectable::*;
import GetPut::*;
import Randomizeable::*;
import Control::*;
import RandomSynth::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef enum {READ, WRITE, BLK_RD, BLK_WR, RMW} CycleKind deriving(Bounded, Bits, Eq);

typedef enum {CLASSIC, CONSTANT, LINEAR, WRAP4, WRAP8, WRAP16, EOB} PipeKind deriving(Bounded, Bits, Eq);

typedef enum {UNKNOWN, ACK, RTY, ERR, TIMEOUT} Status deriving(Bounded, Bits, Eq);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {
		data_t data;
		tag_t tag;
		} TaggedData #(type data_t, type tag_t) deriving (Bounded, Bits, Eq);


typedef Bit#(8) Select;
typedef Bit#(16) Tag;

typedef TaggedData#(Bit#(64),Tag) BusAddr;
typedef TaggedData#(Bool,Tag) BusCycle;
typedef TaggedData#(Bit#(64),Tag) BusData;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {CycleKind kind;
		PipeKind next_cycle;
		BusAddr  addr;
		BusData  data;
		Select   sel;
		Tag      tgc;
		Bool     lock;
		Status   status;
		} WBoneOp deriving (Eq, Bits);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneOpTxRxIFC;
   interface Get#(WBoneOp) tx;
   interface Put#(WBoneOp) rx;
endinterface
      
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Connectable#(WBoneOpTxRxIFC, WBoneOpTxRxIFC);
      module mkConnection#(WBoneOpTxRxIFC left, WBoneOpTxRxIFC right) (Empty);
	 mkConnection(left.tx, right.rx);
	 mkConnection(left.rx, right.tx);
      endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneZBusClientIFC;
   interface ZBusClientIFC#(BusData)  dati;
   interface ZBusClientIFC#(BusData)  dato;
   interface ZBusClientIFC#(Select)   sel;
   interface ZBusClientIFC#(BusAddr)  adr;
   interface ZBusClientIFC#(Bool)     ack;
   interface ZBusClientIFC#(BusCycle) cyc;
   interface ZBusClientIFC#(Bool)     err;
   interface ZBusClientIFC#(Bool)     lock;
   interface ZBusClientIFC#(Bool)     stb;	 
   interface ZBusClientIFC#(Bool)     rty;
   interface ZBusClientIFC#(Bool)     we;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneXActorIFC;
   interface Control cntrl;
   interface WBoneOpTxRxIFC  channel;
   interface WBoneZBusBusIFC bus;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneBusIFC#(type addr_t, type cycle_t, type data_t, type select_t);
   method Action   dati_i(data_t value);
   method data_t   dati_o();
   method Action   dato_i(data_t value);
   method data_t   dato_o();
   method Action   sel_i(select_t value);
   method select_t sel_o();
   method Action   adr_i(addr_t value);
   method addr_t   adr_o();
   method Action   ack_i(Bool value);
   method Bool     ack_o();
   method Action   cyc_i(cycle_t value);
   method cycle_t  cyc_o();
   method Action   err_i(Bool value);
   method Bool     err_o();
   method Action   lock_i(Bool value);
   method Bool     lock_o();
   method Action   stb_i(Bool value);
   method Bool     stb_o();
   method Action   rty_i(Bool value);
   method Bool     rty_o();
   method Action   we_i(Bool value);
   method Bool     we_o();
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneZBusBusIFC;
   interface ZBusBusIFC#(BusData)  dati;
   interface ZBusBusIFC#(BusData)  dato;
   interface ZBusBusIFC#(Select)   sel;
   interface ZBusBusIFC#(BusAddr)  adr;
   interface ZBusBusIFC#(Bool)     ack;
   interface ZBusBusIFC#(BusCycle) cyc;
   interface ZBusBusIFC#(Bool)     err;
   interface ZBusBusIFC#(Bool)     lock;
   interface ZBusBusIFC#(Bool)     stb;	 
   interface ZBusBusIFC#(Bool)     rty;
   interface ZBusBusIFC#(Bool)     we;
endinterface
      
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBoneZBusDualIFC;
   interface WBoneZBusBusIFC    busIFC;
   interface WBoneZBusClientIFC clientIFC;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBoneZBus#(List#(WBoneZBusBusIFC) ifc_list) (Empty);

   function dati_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.dati();
   endfunction

   function dato_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.dato();
   endfunction

   function sel_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.sel();
   endfunction

   function adr_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.adr();
   endfunction

   function ack_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.ack();
   endfunction

   function cyc_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.cyc();
   endfunction
   
   function err_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.err();
   endfunction

   function lock_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.lock();
   endfunction

   function stb_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.stb();
   endfunction

   function rty_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.rty();
   endfunction

   function we_ifc (wb_ifc);
      WBoneZBusBusIFC ifc = wb_ifc;
      return ifc.we();
   endfunction

   mkZBus(map(dati_ifc, ifc_list));
   mkZBus(map(dato_ifc, ifc_list));
   mkZBus(map(sel_ifc, ifc_list));
   mkZBus(map(adr_ifc, ifc_list));
   mkZBus(map(ack_ifc, ifc_list));
   mkZBus(map(cyc_ifc, ifc_list));
   mkZBus(map(err_ifc, ifc_list));
   mkZBus(map(lock_ifc, ifc_list));
   mkZBus(map(stb_ifc, ifc_list));
   mkZBus(map(rty_ifc, ifc_list));
   mkZBus(map(we_ifc, ifc_list));
   
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBoneZBusBuffer (WBoneZBusDualIFC);

   ZBusDualIFC#(BusData)  dati_ifc <- mkZBusBuffer;
   ZBusDualIFC#(BusData)  dato_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Select)   sel_ifc <- mkZBusBuffer;
   ZBusDualIFC#(BusAddr)  adr_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     ack_ifc <- mkZBusBuffer;
   ZBusDualIFC#(BusCycle) cyc_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     err_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     lock_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     stb_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     rty_ifc <- mkZBusBuffer;
   ZBusDualIFC#(Bool)     we_ifc <- mkZBusBuffer;
   
   interface WBoneZBusClientIFC clientIFC;
      interface ZBusClientIFC dati = dati_ifc.clientIFC;
      interface ZBusClientIFC dato = dato_ifc.clientIFC;
      interface ZBusClientIFC sel  = sel_ifc.clientIFC;
      interface ZBusClientIFC adr  = adr_ifc.clientIFC;
      interface ZBusClientIFC ack  = ack_ifc.clientIFC;	    
      interface ZBusClientIFC cyc  = cyc_ifc.clientIFC;
      interface ZBusClientIFC err  = err_ifc.clientIFC;
      interface ZBusClientIFC lock = lock_ifc.clientIFC;
      interface ZBusClientIFC stb  = stb_ifc.clientIFC;
      interface ZBusClientIFC rty  = rty_ifc.clientIFC;
      interface ZBusClientIFC we   = we_ifc.clientIFC;
   endinterface
   
   interface WBoneZBusBusIFC busIFC;
      interface ZBusBusIFC dati = dati_ifc.busIFC;
      interface ZBusBusIFC dato = dato_ifc.busIFC;
      interface ZBusBusIFC sel  = sel_ifc.busIFC;
      interface ZBusBusIFC adr  = adr_ifc.busIFC;
      interface ZBusBusIFC ack  = ack_ifc.busIFC;	    
      interface ZBusBusIFC cyc  = cyc_ifc.busIFC;
      interface ZBusBusIFC err  = err_ifc.busIFC;
      interface ZBusBusIFC lock = lock_ifc.busIFC;
      interface ZBusBusIFC stb  = stb_ifc.busIFC;
      interface ZBusBusIFC rty  = rty_ifc.busIFC;
      interface ZBusBusIFC we   = we_ifc.busIFC;
   endinterface

endmodule
	 
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function String showCycleKind (CycleKind kind);

   String result;
   
   case (kind)
      READ:    result = "READ";
      WRITE:   result = "WRITE";
      BLK_RD:  result = "BLK_RD";
      BLK_WR:  result = "BLK_RW";
      RMW:     result = "RMW";
      default: result = "INVALID";
   endcase
   return result;

endfunction

function String showPipeKind (PipeKind kind);
   
   String result;
   
   case (kind)
      CLASSIC:  result = "CLASSIC";
      CONSTANT: result = "CONSTANT";
      LINEAR:   result = "LINEAR";
      WRAP4:    result = "WRAP4";
      WRAP8:    result = "WRAP8";
      WRAP16:   result = "WRAP16";
      EOB:      result = "EOB";
      default:  result = "INVALID";
   endcase
   return result;

endfunction

function String showStatus (Status status);
   
   String result;
   
   case (status)
      UNKNOWN: result = "UNKNOWN";
      ACK:     result = "ACK";
      RTY:     result = "RTY";
      ERR:     result = "ERR";
      TIMEOUT: result = "TIMEOUT";
      default: result = "INVALID";
   endcase
   return result;

endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action displayWBoneOp (WBoneOp op);

   $display("[WBoneOp kind: %0s\n   next_cycle: %0s\n         addr: %h\n         data: %h\n          sel: %b\n          tgc: %d\n         lock: %0s\n       status: %0s]",
	    showCycleKind(op.kind),
	    showPipeKind(op.next_cycle), 
	    op.addr.data,
	    op.data.data,
	    op.sel,
	    op.tgc,
	    showBool(op.lock),
	    showStatus(op.status)
	    );

endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function WBoneOp createWBoneOp (WBoneZBusClientIFC ifc);

   let kind = READ;
   let data = ifc.dati.get();

   if (ifc.we.get()) 
      begin
	 kind = WRITE;
	 data = ifc.dato.get();
      end
   else
      begin
	 kind = READ;
	 data = ifc.dati.get();
      end

   let next_cycle = CLASSIC;
   let addr       = ifc.adr.get();
   let sel        = ifc.sel.get();
   let cycle      = ifc.cyc.get();
   let lock       = ifc.lock.get();

   let status = UNKNOWN;
   if (ifc.ack.get()) status = ACK;
   if (ifc.err.get()) status = ERR;
   
   let wboneop = WBoneOp {kind:       kind,
			  next_cycle: next_cycle,
			  addr:       addr,
			  data:       data,
			  sel:        sel,
			  tgc:        cycle.tag,
			  lock:       lock,
			  status:     status
			  };

   return wboneop;

endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Randomizeable#(WBoneOp);
      module mkRandomizer (Randomize#(WBoneOp));
	 
	 Randomize#(CycleKind) kind_gen       <- mkGenericRandomizer_Synth;
	 Randomize#(PipeKind)  next_cycle_gen <- mkGenericRandomizer_Synth;
	 Randomize#(BusAddr)   addr_gen       <- mkGenericRandomizer_Synth;
	 Randomize#(BusData)   data_gen       <- mkGenericRandomizer_Synth;
	 Randomize#(Select)    sel_gen        <- mkGenericRandomizer_Synth;
	 Randomize#(Bool)      lock_gen       <- mkGenericRandomizer_Synth;
	 Randomize#(Status)    status_gen     <- mkGenericRandomizer_Synth;
	 
	 interface Control cntrl;
	    method Action init();
	       kind_gen.cntrl.init();
	       next_cycle_gen.cntrl.init();
	       addr_gen.cntrl.init();
	       data_gen.cntrl.init();
	       sel_gen.cntrl.init();
	       lock_gen.cntrl.init();
	       status_gen.cntrl.init();
	    endmethod
	 endinterface
	 
	 method ActionValue#(WBoneOp) next ();

	    let kind       <- kind_gen.next();
	    let next_cycle <- next_cycle_gen.next();
	    let addr       <- addr_gen.next();
	    let data       <- data_gen.next();
	    let sel        <- sel_gen.next();
	    let lock       <- lock_gen.next();
	    let status     <- status_gen.next();
	    
	    let wboneop = WBoneOp {kind:       kind,
				   next_cycle: next_cycle,
				   addr:       addr,
				   data:       data,
				   sel:        sel,
				   tgc:        unpack(0),
				   lock:       lock,
				   status:     status
				   };

	    return wboneop;
	    
	 endmethod

      endmodule
endinstance

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

