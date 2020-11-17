////////////////////////////////////////////////////////////////////////////////
//  Author        : Todd Snyder
//  Description   : Creates Block RAMS for use in Xilinx FPGAs
////////////////////////////////////////////////////////////////////////////////

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import GetPut            ::*;
import ClientServer      ::*;
import FIFOF             ::*;


////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typedef struct {
		Bool write;
		addr address;
		data datain;
		} BRAMRequest#(type addr, type data) deriving(Bits, Eq);

typedef struct {
		Bit#(n) writeen;
		addr    address;
		data    datain;
		} BRAMRequestBE#(type addr, type data, numeric type n) deriving (Bits, Eq);

typedef Server#(BRAMRequest#(addr, data), data) BRAMServer#(type addr, type data);
typedef Client#(BRAMRequest#(addr, data), data) BRAMClient#(type addr, type data);

typedef Server#(BRAMRequestBE#(addr, data, n), data) BRAMServerBE#(type addr, type data, numeric type n);
typedef Client#(BRAMRequestBE#(addr, data, n), data) BRAMClientBE#(type addr, type data, numeric type n);


////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
/// Single Write Enable Interfaces
////////////////////////////////////////////////////////////////////////////////
(* always_ready *)
interface BRAM_PORT#(type addr, type data);
   method Action put(Bool write, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT

interface BRAM#(type addr, type data);
   interface BRAMServer#(addr, data) portA;
   interface BRAMServer#(addr, data) portB;
endinterface: BRAM

interface BRAM_DUAL_PORT#(type addr, type data);
   interface BRAM_PORT#(addr, data) a;
   interface BRAM_PORT#(addr, data) b;
endinterface

interface BRAM2Port#(type addr, type data);
   interface BRAMServer#(addr, data) portA;
   interface BRAMServer#(addr, data) portB;
endinterface: BRAM2Port

interface BRAM1Port#(type addr, type data);
   interface BRAMServer#(addr, data) portA;
endinterface: BRAM1Port

////////////////////////////////////////////////////////////////////////////////
/// Byte Write Enable Interfaces
////////////////////////////////////////////////////////////////////////////////
(* always_ready *)
interface BRAM_PORT_BE#(type addr, type data, numeric type n);
   method Action put(Bit#(n) writeen, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT_BE

interface BRAM_DUAL_PORT_BE#(type addr, type data, numeric type n);
   interface BRAM_PORT_BE#(addr, data, n) a;
   interface BRAM_PORT_BE#(addr, data, n) b;
endinterface

interface BRAM_BE#(type addr, type data, numeric type n);
   interface BRAMServerBE#(addr, data, n) portA;
   interface BRAMServerBE#(addr, data, n) portB;
endinterface: BRAM_BE

interface BRAM2PortBE#(type addr, type data, numeric type n);
   interface BRAMServerBE#(addr, data, n) portA;
   interface BRAMServerBE#(addr, data, n) portB;
endinterface: BRAM2PortBE

interface BRAM1PortBE#(type addr, type data, numeric type n);
   interface BRAMServerBE#(addr, data, n) portA;
endinterface: BRAM1PortBE

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Helper Modules
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBypassFIFOF_ (FIFOF#(a))
   provisos (Bits#(a,sa));

   // STATE ----------------

   Reg#(Maybe#(a))   taggedReg <- mkReg (tagged Invalid); // the FIFO
   RWire#(a)         rw_enq    <- mkRWire;                // enq method signal
   PulseWire         pw_deq    <- mkPulseWire;            // deq method signal

   Bool enq_ok = (! isValid (taggedReg));
   Bool deq_ok = (isValid (taggedReg) || isValid (rw_enq.wget));

   // RULES ----------------

   rule rule_enq (rw_enq.wget matches tagged Valid .v &&& (! pw_deq));
     taggedReg <= tagged Valid v;
   endrule

   rule rule_deq (pw_deq);
     taggedReg <= tagged Invalid;
   endrule

   // INTERFACE ----------------

   method Action enq(v) if (enq_ok);
      rw_enq.wset(v);
   endmethod

   method Action deq() if (deq_ok);
      pw_deq.send ();
   endmethod

   method first() if (deq_ok);
      return (rw_enq.wget matches tagged Valid .v
              ? v
              : fromMaybe (?, taggedReg));
   endmethod

   method notFull ();
      return enq_ok;
   endmethod

   method notEmpty ();
      return deq_ok;
   endmethod

   method Action clear();
      taggedReg <= tagged Invalid;
   endmethod

endmodule

module mkBypassFIFOF2_ (FIFOF#(a))
   provisos (Bits#(a,sa));

   // STATE ----------------

   Reg#(Maybe#(a))   taggedReg0 <- mkReg (tagged Invalid); // the FIFO
   Reg#(Maybe#(a))   taggedReg1 <- mkReg (tagged Invalid); // the FIFO
   RWire#(a)         rw_enq    <- mkRWire;                // enq method signal
   PulseWire         pw_deq    <- mkPulseWire;            // deq method signal

   Bool enq_ok = (! isValid (taggedReg1));
   Bool enq_ok_outside = (! isValid (taggedReg0));
   Bool deq_ok = (isValid (taggedReg0) || isValid (rw_enq.wget));

   // RULES ----------------

   rule rule_enq (rw_enq.wget matches tagged Valid .v &&& (! pw_deq));
      if (taggedReg0 matches tagged Valid .*)
	 taggedReg1 <= tagged Valid v;
      else
	 taggedReg0 <= tagged Valid v;
   endrule

   rule rule_deq (pw_deq);
      taggedReg1 <= tagged Invalid;
      taggedReg0 <= taggedReg1;
   endrule

   // INTERFACE ----------------

   method Action enq(v) if (enq_ok);
      rw_enq.wset(v);
   endmethod

   method Action deq() if (deq_ok);
      pw_deq.send ();
   endmethod

   method first() if (deq_ok);
      return (rw_enq.wget matches tagged Valid .v
              ? v
              : fromMaybe (?, taggedReg0));
   endmethod

   method notFull ();
      return enq_ok_outside;
   endmethod

   method notEmpty ();
      return deq_ok;
   endmethod

   method Action clear();
      taggedReg0 <= tagged Invalid;
      taggedReg1 <= tagged Invalid;
   endmethod

endmodule

module mkBypassFIFOF3_ (FIFOF#(a))
   provisos (Bits#(a,sa));

   // STATE ----------------

   Reg#(Maybe#(a))   taggedReg0 <- mkReg (tagged Invalid); // the FIFO
   Reg#(Maybe#(a))   taggedReg1 <- mkReg (tagged Invalid); // the FIFO
   Reg#(Maybe#(a))   taggedReg2 <- mkReg (tagged Invalid); // the FIFO
   RWire#(a)         rw_enq    <- mkRWire;                // enq method signal
   PulseWire         pw_deq    <- mkPulseWire;            // deq method signal

   Bool enq_ok = (! isValid (taggedReg2));
   Bool enq_ok_outside = (! isValid (taggedReg1));
   Bool deq_ok = (isValid (taggedReg0) || isValid (rw_enq.wget));

   // RULES ----------------

   rule rule_enq (rw_enq.wget matches tagged Valid .v &&& (! pw_deq));
      if (taggedReg1 matches tagged Valid .*)
	 taggedReg2 <= tagged Valid v;
      else if (taggedReg0 matches tagged Valid .*)
	 taggedReg1 <= tagged Valid v;
      else
	 taggedReg0 <= tagged Valid v;
   endrule

   rule rule_deq (pw_deq);
      taggedReg2 <= tagged Invalid;
      taggedReg1 <= taggedReg2;
      taggedReg0 <= taggedReg1;
   endrule

   // INTERFACE ----------------

   method Action enq(v) if (enq_ok);
      rw_enq.wset(v);
   endmethod

   method Action deq() if (deq_ok);
      pw_deq.send ();
   endmethod

   method first() if (deq_ok);
      return (rw_enq.wget matches tagged Valid .v
              ? v
              : fromMaybe (?, taggedReg0));
   endmethod

   method notFull ();
      return enq_ok_outside;
   endmethod

   method notEmpty ();
      return deq_ok;
   endmethod

   method Action clear();
      taggedReg0 <= tagged Invalid;
      taggedReg1 <= tagged Invalid;
      taggedReg2 <= tagged Invalid;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Dual Ported BRAM Definition
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM2 =
module vBRAM2#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);

   interface BRAM_PORT a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b

   schedule (a_put, a_read) CF (a_put, a_read);
   schedule (b_put, b_read) CF (b_put, b_read);

endmodule: vBRAM2

import "BVI" BRAM2Load =
module vBRAM2Load#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file, Integer binary)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter FILENAME   = file;
   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);
   parameter BINARY     = binary;

   interface BRAM_PORT a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b

   schedule (a_put, a_read) CF (a_put, a_read);
   schedule (b_put, b_read) CF (b_put, b_read);

endmodule: vBRAM2Load

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Dual-Ported BRAM module source definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
(* no_default_clock, no_default_reset *)
module mkSyncBRAM2#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   let _m <- mkSyncBRAM(hasOutputRegister, clkA, rstNA, clkB, rstNB);

   interface portA = _m.portA;
   interface portB = _m.portB;
endmodule

(* no_default_clock, no_default_reset *)
module mkSyncBRAM#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_DUAL_PORT#(addr, data)            memory               = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM0(hasOutputRegister, clkA, rstNA, clkB, rstNB);
   else
      memory              <- vBRAM2(hasOutputRegister, clkA, rstNA, clkB, rstNB);

   FIFOF#(BRAMRequest#(addr, data))       fifoReqA            <- mkBypassFIFOF_(clocked_by clkA, reset_by rstNA);
   FIFOF#(data)                           fifoRespA           <- mkBypassFIFOF3_(clocked_by clkA, reset_by rstNA);

   Wire#(addr)                            wAddrA              <- mkDWire(unpack(0), clocked_by clkA, reset_by rstNA);
   PulseWire                              pwActiveA           <- mkPulseWire(clocked_by clkA, reset_by rstNA);
   Reg#(Bool)                             rActiveA            <- mkReg(False, clocked_by clkA, reset_by rstNA);
   Reg#(Bool)                             rActiveAD1          <- mkReg(False, clocked_by clkA, reset_by rstNA);
   Wire#(data)                            wDataA              <- mkDWire(unpack(0), clocked_by clkA, reset_by rstNA);
   Wire#(Bool)                            wWriteA             <- mkDWire(False, clocked_by clkA, reset_by rstNA);

   FIFOF#(BRAMRequest#(addr, data))       fifoReqB            <- mkBypassFIFOF_(clocked_by clkB, reset_by rstNB);
   FIFOF#(data)                           fifoRespB           <- mkBypassFIFOF3_(clocked_by clkB, reset_by rstNB);

   Wire#(addr)                            wAddrB              <- mkDWire(unpack(0), clocked_by clkB, reset_by rstNB);
   PulseWire                              pwActiveB           <- mkPulseWire(clocked_by clkB, reset_by rstNB);
   Reg#(Bool)                             rActiveB            <- mkReg(False, clocked_by clkB, reset_by rstNB);
   Reg#(Bool)                             rActiveBD1          <- mkReg(False, clocked_by clkB, reset_by rstNB);
   Wire#(data)                            wDataB              <- mkDWire(unpack(0), clocked_by clkB, reset_by rstNB);
   Wire#(Bool)                            wWriteB             <- mkDWire(False, clocked_by clkB, reset_by rstNB);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port A)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect_A;
      memory.a.put(wWriteA, wAddrA, wDataA);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active_A;
      rActiveA <= pwActiveA;
      rActiveAD1 <= rActiveA;
   endrule

   rule get_read_response_A((rActiveA && !hasOutputRegister) || (rActiveAD1 && hasOutputRegister));
      fifoRespA.enq(memory.a.read());
   endrule

   rule process_read_request_A(!fifoReqA.first.write && fifoRespA.notFull);
      let request = fifoReqA.first; fifoReqA.deq;
      wAddrA <= request.address;
      pwActiveA.send;
   endrule

   rule process_write_request_A(fifoReqA.first.write && fifoRespA.notFull);
      let request = fifoReqA.first; fifoReqA.deq;
      wAddrA  <= request.address;
      wDataA  <= request.datain;
      wWriteA <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port B)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect_B;
      memory.b.put(wWriteB, wAddrB, wDataB);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active_B;
      rActiveB <= pwActiveB;
      rActiveBD1 <= rActiveB;
   endrule

   rule get_read_response_B((rActiveB && !hasOutputRegister) || (rActiveBD1 && hasOutputRegister));
      fifoRespB.enq(memory.b.read());
   endrule

   rule process_read_request_B(!fifoReqB.first.write && fifoRespB.notFull);
      let request = fifoReqB.first; fifoReqB.deq;
      wAddrB <= request.address;
      pwActiveB.send;
   endrule

   rule process_write_request_B(fifoReqB.first.write && fifoRespB.notFull);
      let request = fifoReqB.first; fifoReqB.deq;
      wAddrB  <= request.address;
      wDataB  <= request.datain;
      wWriteB <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServer portA;
      interface Put request  = toPut(fifoReqA);
      interface Get response = toGet(fifoRespA);
   endinterface

   interface BRAMServer portB;
      interface Put request  = toPut(fifoReqB);
      interface Get response = toGet(fifoRespB);
   endinterface

endmodule: mkSyncBRAM

(* no_default_clock, no_default_reset *)
module mkSyncBRAM2LoadEither#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file, Integer binary)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   let _m <- mkSyncBRAMLoadEither(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);

   interface portA = _m.portA;
   interface portB = _m.portB;
endmodule: mkSyncBRAM2LoadEither

(* no_default_clock, no_default_reset *)
module mkSyncBRAMLoadEither#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file, Integer binary)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_DUAL_PORT#(addr, data)            memory                  = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM0Load(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);
   else
      memory              <- vBRAM2Load(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);

   FIFOF#(BRAMRequest#(addr, data))       fifoReqA            <- mkBypassFIFOF_(clocked_by clkA, reset_by rstNA);
   FIFOF#(data)                           fifoRespA           <- mkBypassFIFOF3_(clocked_by clkA, reset_by rstNA);

   Wire#(addr)                            wAddrA              <- mkDWire(unpack(0), clocked_by clkA, reset_by rstNA);
   PulseWire                              pwActiveA           <- mkPulseWire(clocked_by clkA, reset_by rstNA);
   Reg#(Bool)                             rActiveA            <- mkReg(False, clocked_by clkA, reset_by rstNA);
   Reg#(Bool)                             rActiveAD1          <- mkReg(False, clocked_by clkA, reset_by rstNA);
   Wire#(data)                            wDataA              <- mkDWire(unpack(0), clocked_by clkA, reset_by rstNA);
   Wire#(Bool)                            wWriteA             <- mkDWire(False, clocked_by clkA, reset_by rstNA);

   FIFOF#(BRAMRequest#(addr, data))       fifoReqB            <- mkBypassFIFOF_(clocked_by clkB, reset_by rstNB);
   FIFOF#(data)                           fifoRespB           <- mkBypassFIFOF3_(clocked_by clkB, reset_by rstNB);

   Wire#(addr)                            wAddrB              <- mkDWire(unpack(0), clocked_by clkB, reset_by rstNB);
   PulseWire                              pwActiveB           <- mkPulseWire(clocked_by clkB, reset_by rstNB);
   Reg#(Bool)                             rActiveB            <- mkReg(False, clocked_by clkB, reset_by rstNB);
   Reg#(Bool)                             rActiveBD1          <- mkReg(False, clocked_by clkB, reset_by rstNB);
   Wire#(data)                            wDataB              <- mkDWire(unpack(0), clocked_by clkB, reset_by rstNB);
   Wire#(Bool)                            wWriteB             <- mkDWire(False, clocked_by clkB, reset_by rstNB);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port A)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect_A;
      memory.a.put(wWriteA, wAddrA, wDataA);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active_A;
      rActiveA <= pwActiveA;
      rActiveAD1 <= rActiveA;
   endrule

   rule get_read_response_A((rActiveA && !hasOutputRegister) || (rActiveAD1 && hasOutputRegister));
      fifoRespA.enq(memory.a.read());
   endrule

   rule process_read_request_A(!fifoReqA.first.write && fifoRespA.notFull);
      let request = fifoReqA.first; fifoReqA.deq;
      wAddrA <= request.address;
      pwActiveA.send;
   endrule

   rule process_write_request_A(fifoReqA.first.write && fifoRespA.notFull);
      let request = fifoReqA.first; fifoReqA.deq;
      wAddrA  <= request.address;
      wDataA  <= request.datain;
      wWriteA <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port A)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect_B;
      memory.b.put(wWriteB, wAddrB, wDataB);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active_B;
      rActiveB <= pwActiveB;
      rActiveBD1 <= rActiveB;
   endrule

   rule get_read_response_B((rActiveB && !hasOutputRegister) || (rActiveBD1 && hasOutputRegister));
      fifoRespB.enq(memory.b.read());
   endrule

   rule process_read_request_B(!fifoReqB.first.write && fifoRespB.notFull);
      let request = fifoReqB.first; fifoReqB.deq;
      wAddrB <= request.address;
      pwActiveB.send;
   endrule

   rule process_write_request_B(fifoReqB.first.write && fifoRespB.notFull);
      let request = fifoReqB.first; fifoReqB.deq;
      wAddrB  <= request.address;
      wDataB  <= request.datain;
      wWriteB <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServer portA;
      interface Put request  = toPut(fifoReqA);
      interface Get response = toGet(fifoRespA);
   endinterface

   interface BRAMServer portB;
      interface Put request  = toPut(fifoReqB);
      interface Get response = toGet(fifoRespB);
   endinterface

endmodule: mkSyncBRAMLoadEither


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Dual-ported BRAM module definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBRAM2#(Bool hasOutputRegister)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m  <- mkSyncBRAM2(hasOutputRegister, clk, rst, clk, rst);
   return _m;
endmodule

module mkBRAM2LoadHex#(Bool hasOutputRegister, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m <- mkSyncBRAM2LoadHex(hasOutputRegister, clk, rst, clk, rst, file);
   return _m;
endmodule: mkBRAM2LoadHex

module mkBRAM2LoadBin#(Bool hasOutputRegister, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m <- mkSyncBRAM2LoadBin(hasOutputRegister, clk, rst, clk, rst, file);
   return _m;
endmodule: mkBRAM2LoadBin

(* no_default_clock, no_default_reset *)
module mkSyncBRAM2LoadHex#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAM2LoadEither(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, 0);
   return _m;
endmodule: mkSyncBRAM2LoadHex

(* no_default_clock, no_default_reset *)
module mkSyncBRAM2LoadBin#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAM2LoadEither(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, 1);
   return _m;
endmodule: mkSyncBRAM2LoadBin

module mkBRAM2Load#(Bool hasOutputRegister, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM2LoadHex(hasOutputRegister, file);
   return _m;
endmodule: mkBRAM2Load

(* no_default_clock, no_default_reset *)
module mkSyncBRAM2Load#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM2Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAM2LoadHex(hasOutputRegister, clkA, rstNA, clkB, rstNB, file);
   return _m;
endmodule: mkSyncBRAM2Load

module mkBRAM#(Bool hasOutputRegister)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m  <- mkSyncBRAM(hasOutputRegister, clk, rst, clk, rst);
   return _m;
endmodule

module mkBRAMLoadHex#(Bool hasOutputRegister, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m <- mkSyncBRAMLoadHex(hasOutputRegister, clk, rst, clk, rst, file);
   return _m;
endmodule: mkBRAMLoadHex

module mkBRAMLoadBin#(Bool hasOutputRegister, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   let _m <- mkSyncBRAMLoadBin(hasOutputRegister, clk, rst, clk, rst, file);
   return _m;
endmodule: mkBRAMLoadBin

(* no_default_clock, no_default_reset *)
module mkSyncBRAMLoadHex#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAMLoadEither(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, 0);
   return _m;
endmodule: mkSyncBRAMLoadHex

(* no_default_clock, no_default_reset *)
module mkSyncBRAMLoadBin#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAMLoadEither(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, 1);
   return _m;
endmodule: mkSyncBRAMLoadBin

module mkBRAMLoad#(Bool hasOutputRegister, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAMLoadHex(hasOutputRegister, file);
   return _m;
endmodule: mkBRAMLoad

(* no_default_clock, no_default_reset *)
module mkSyncBRAMLoad#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file)(BRAM#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkSyncBRAMLoadHex(hasOutputRegister, clkA, rstNA, clkB, rstNB, file);
   return _m;
endmodule: mkSyncBRAMLoad

module mkBRAM0#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   let _m <- mkBRAM20(hasOutputRegister, clkA, rstNA, clkB, rstNB);
   return _m;
endmodule: mkBRAM0

module mkBRAM20#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   interface BRAM_PORT a;
      method Action put(write, address, datain);
	 noAction;
      endmethod
      method data   read();
	 return ?;
      endmethod
   endinterface: a

   interface BRAM_PORT b;
      method Action put(write, address, datain);
	 noAction;
      endmethod
      method data   read();
	 return ?;
      endmethod
   endinterface: b

endmodule: mkBRAM20

module mkBRAM0Load#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file, Integer binary)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   let _m <- mkBRAM20Load(hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);
   return _m;
endmodule: mkBRAM0Load

module mkBRAM20Load#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String file, Integer binary)(BRAM_DUAL_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   interface BRAM_PORT a;
      method Action put(write, address, datain);
	 noAction;
      endmethod
      method data   read();
	 return ?;
      endmethod
   endinterface: a

   interface BRAM_PORT b;
      method Action put(write, address, datain);
	 noAction;
      endmethod
      method data   read();
	 return ?;
      endmethod
   endinterface: b

endmodule: mkBRAM20Load




////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single Ported BRAM Definition
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM1 =
module vBRAM1#(Bool hasOutputRegister)(BRAM_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO  read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (put, read);

endmodule: vBRAM1

import "BVI" BRAM1Load =
module vBRAM1Load#(Bool hasOutputRegister, String file, Integer binary)(BRAM_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter FILENAME   = file;
   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);
   parameter BINARY     = binary;

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (put, read);

endmodule: vBRAM1Load

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single-Ported BRAM module source definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBRAM1#(Bool hasOutputRegister)(BRAM1Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_PORT#(addr, data)                 memory               = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM10(hasOutputRegister);
   else
      memory              <- vBRAM1(hasOutputRegister);

   FIFOF#(BRAMRequest#(addr, data))       fifoReq             <- mkBypassFIFOF_;
   FIFOF#(data)                           fifoResp            <- mkBypassFIFOF3_;

   Wire#(addr)                            wAddr               <- mkDWire(unpack(0));
   PulseWire                              pwActive            <- mkPulseWire;
   Reg#(Bool)                             rActive             <- mkReg(False);
   Reg#(Bool)                             rActiveD1           <- mkReg(False);
   Wire#(data)                            wData               <- mkDWire(unpack(0));
   Wire#(Bool)                            wWrite              <- mkDWire(False);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect;
      memory.put(wWrite, wAddr, wData);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active;
      rActive <= pwActive;
      rActiveD1 <= rActive;
   endrule

   rule get_read_response((rActive && !hasOutputRegister) || (rActiveD1 && hasOutputRegister));
      fifoResp.enq(memory.read());
   endrule

   rule process_read_request(!fifoReq.first.write && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr <= request.address;
      pwActive.send;
   endrule

   rule process_write_request(fifoReq.first.write && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr  <= request.address;
      wData  <= request.datain;
      wWrite <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServer portA;
      interface Put request  = toPut(fifoReq);
      interface Get response = toGet(fifoResp);
   endinterface

endmodule: mkBRAM1

module mkBRAM1LoadEither#(Bool hasOutputRegister, String file, Integer binary)(BRAM1Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_PORT#(addr, data)                 memory                  = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM10Load(hasOutputRegister, file, binary);
   else
      memory              <- vBRAM1Load(hasOutputRegister, file, binary);

   FIFOF#(BRAMRequest#(addr, data))       fifoReq             <- mkBypassFIFOF_;
   FIFOF#(data)                           fifoResp            <- mkBypassFIFOF3_;

   Wire#(addr)                            wAddr               <- mkDWire(unpack(0));
   PulseWire                              pwActive            <- mkPulseWire;
   Reg#(Bool)                             rActive             <- mkReg(False);
   Reg#(Bool)                             rActiveD1           <- mkReg(False);
   Wire#(data)                            wData               <- mkDWire(unpack(0));
   Wire#(Bool)                            wWrite              <- mkDWire(False);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port A)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect;
      memory.put(wWrite, wAddr, wData);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active;
      rActive   <= pwActive;
      rActiveD1 <= rActive;
   endrule

   rule get_read_response((rActive && !hasOutputRegister) || (rActiveD1 && hasOutputRegister));
      fifoResp.enq(memory.read());
   endrule

   rule process_read_request(!fifoReq.first.write && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr <= request.address;
      pwActive.send;
   endrule

   rule process_write_request(fifoReq.first.write && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr  <= request.address;
      wData  <= request.datain;
      wWrite <= True;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServer portA;
      interface Put request  = toPut(fifoReq);
      interface Get response = toGet(fifoResp);
   endinterface

endmodule: mkBRAM1LoadEither


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single-ported BRAM module definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBRAM1LoadHex#(Bool hasOutputRegister, String file)(BRAM1Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1LoadEither(hasOutputRegister, file, 0);
   return _m;
endmodule: mkBRAM1LoadHex

module mkBRAM1LoadBin#(Bool hasOutputRegister, String file)(BRAM1Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1LoadEither(hasOutputRegister, file, 1);
   return _m;
endmodule: mkBRAM1LoadBin

module mkBRAM1Load#(Bool hasOutputRegister, String file)(BRAM1Port#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1LoadHex(hasOutputRegister, file);
   return _m;
endmodule: mkBRAM1Load

module mkBRAM10#(Bool hasOutputRegister)(BRAM_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   method Action put(write, address, datain);
      noAction;
   endmethod
   method data   read();
      return ?;
   endmethod

endmodule: mkBRAM10


module mkBRAM10Load#(Bool hasOutputRegister, String file, Integer binary)(BRAM_PORT#(addr, data))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz)
	    );

   method Action put(write, address, datain);
      noAction;
   endmethod
   method data   read();
      return ?;
   endmethod

endmodule: mkBRAM10Load


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single Ported BRAM Byte Enabled Definition
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM1BE =
module vBRAM1BE#(Bool hasOutputRegister)(BRAM_PORT_BE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, chunk_sz),
	    Mul#(chunk_sz, n, data_sz)
	    );

   // This is currently a bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) error("You cannot instance a write enabled BRAM with fewer than 1 write enable or greater than 4 write enables.");

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO  read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (put, read);

endmodule: vBRAM1BE

import "BVI" BRAM1BELoad =
module vBRAM1BELoad#(Bool hasOutputRegister, String file, Integer binary)(BRAM_PORT_BE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, chunk_sz),
	    Mul#(chunk_sz, n, data_sz)
	    );
   // This is currently a bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) error("You cannot instance a write enabled BRAM with fewer than 1 write enable or greater than 4 write enables.");

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter FILENAME   = file;
   parameter PIPELINED  = pack(hasOutputRegister);
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = 2 ** valueof(addr_sz);
   parameter BINARY     = binary;

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (put, read);

endmodule: vBRAM1BELoad

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single-Ported BRAM with byte enables module source definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBRAM1BE#(Bool hasOutputRegister)(BRAM1PortBE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, be_sz),
	    Mul#(n, be_sz, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_PORT_BE#(addr, data, n)           memory               = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM10BE(hasOutputRegister);
   else
      memory              <- vBRAM1BE(hasOutputRegister);

   FIFOF#(BRAMRequestBE#(addr, data, n))  fifoReq             <- mkBypassFIFOF_;
   FIFOF#(data)                           fifoResp            <- mkBypassFIFOF3_;

   Wire#(addr)                            wAddr               <- mkDWire(unpack(0));
   PulseWire                              pwActive            <- mkPulseWire;
   Reg#(Bool)                             rActive             <- mkReg(False);
   Reg#(Bool)                             rActiveD1           <- mkReg(False);
   Wire#(data)                            wData               <- mkDWire(unpack(0));
   Wire#(Bit#(n))                         wWrite              <- mkDWire('0);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect;
      memory.put(wWrite, wAddr, wData);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active;
      rActive   <= pwActive;
      rActiveD1 <= rActive;
   endrule

   rule get_read_response((rActive && !hasOutputRegister) || (rActiveD1 && hasOutputRegister));
      fifoResp.enq(memory.read());
   endrule

   rule process_read_request(fifoReq.first.writeen == 0 && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr <= request.address;
      pwActive.send;
   endrule

   rule process_write_request(fifoReq.first.writeen != 0 && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr  <= request.address;
      wData  <= request.datain;
      wWrite <= request.writeen;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServerBE portA;
      interface Put request  = toPut(fifoReq);
      interface Get response = toGet(fifoResp);
   endinterface

endmodule: mkBRAM1BE

module mkBRAM1BELoadEither#(Bool hasOutputRegister, String file, Integer binary)(BRAM1PortBE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, be_sz),
	    Mul#(n, be_sz, data_sz),
	    Bounded#(addr)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   BRAM_PORT_BE#(addr, data, n)           memory                  = ?;

   if (valueof(addr_sz) == 0 || valueof(data_sz) == 0)
      memory              <- mkBRAM10BELoad(hasOutputRegister, file, binary);
   else
      memory              <- vBRAM1BELoad(hasOutputRegister, file, binary);

   FIFOF#(BRAMRequestBE#(addr, data, n))  fifoReq             <- mkBypassFIFOF_;
   FIFOF#(data)                           fifoResp            <- mkBypassFIFOF3_;

   Wire#(addr)                            wAddr               <- mkDWire(unpack(0));
   PulseWire                              pwActive            <- mkPulseWire;
   Reg#(Bool)                             rActive             <- mkReg(False);
   Reg#(Bool)                             rActiveD1           <- mkReg(False);
   Wire#(data)                            wData               <- mkDWire(unpack(0));
   Wire#(Bit#(n))                         wWrite              <- mkDWire('0);

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules (Port A)
   ////////////////////////////////////////////////////////////////////////////////
   (* no_implicit_conditions, fire_when_enabled *)
   rule connect;
      memory.put(wWrite, wAddr, wData);
   endrule

   (* no_implicit_conditions, fire_when_enabled *)
   rule register_active;
      rActive   <= pwActive;
      rActiveD1 <= rActive;
   endrule

   rule get_read_response((rActive && !hasOutputRegister) || (rActiveD1 && hasOutputRegister));
      fifoResp.enq(memory.read());
   endrule

   rule process_read_request(fifoReq.first.writeen == 0 && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr <= request.address;
      pwActive.send;
   endrule

   rule process_write_request(fifoReq.first.writeen != 0 && fifoResp.notFull);
      let request = fifoReq.first; fifoReq.deq;
      wAddr  <= request.address;
      wData  <= request.datain;
      wWrite <= request.writeen;
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface BRAMServerBE portA;
      interface Put request  = toPut(fifoReq);
      interface Get response = toGet(fifoResp);
   endinterface

endmodule: mkBRAM1BELoadEither

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single-ported BRAM with Byte Enables module definitions
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkBRAM1BELoadHex#(Bool hasOutputRegister, String file)(BRAM1PortBE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, be_sz),
	    Mul#(n, be_sz, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1BELoadEither(hasOutputRegister, file, 0);
   return _m;
endmodule: mkBRAM1BELoadHex

module mkBRAM1BELoadBin#(Bool hasOutputRegister, String file)(BRAM1PortBE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, be_sz),
	    Mul#(n, be_sz, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1BELoadEither(hasOutputRegister, file, 1);
   return _m;
endmodule: mkBRAM1BELoadBin

module mkBRAM1BELoad#(Bool hasOutputRegister, String file)(BRAM1PortBE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, be_sz),
	    Mul#(n, be_sz, data_sz),
	    Bounded#(addr)
	    );
   let _m <- mkBRAM1BELoadHex(hasOutputRegister, file);
   return _m;
endmodule: mkBRAM1BELoad

module mkBRAM10BE#(Bool hasOutputRegister)(BRAM_PORT_BE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, chunk_sz),
	    Mul#(chunk_sz, n, data_sz)
	    );

   method Action put(write, address, datain);
      noAction;
   endmethod
   method data   read();
      return ?;
   endmethod

endmodule: mkBRAM10BE


module mkBRAM10BELoad#(Bool hasOutputRegister, String file, Integer binary)(BRAM_PORT_BE#(addr, data, n))
   provisos(
	    Bits#(addr, addr_sz),
	    Bits#(data, data_sz),
	    Div#(data_sz, n, chunk_sz),
	    Mul#(chunk_sz, n, data_sz)
	    );

   method Action put(write, address, datain);
      noAction;
   endmethod
   method data   read();
      return ?;
   endmethod

endmodule: mkBRAM10BELoad
