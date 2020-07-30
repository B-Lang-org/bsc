package Mpmc_NPI;

`include "MPMC.defines"

import FIFOF::*;
import SpecialFIFOs::*;
import GetPut::*;
import DReg::*;
import Vector::*;
import TLM::*;
import Clocks::*;
import Connectable::*;

// Configurable parameters needed by BSV code (some of them also required by
// the Verilog):

`define BANK_WIDTH 2       // # of memory bank addr bits
`define CKE_WIDTH  1       // # of memory clock enable outputs
`define CLK_WIDTH  2       // # of clock outputs
`define CS_WIDTH   1       // # of total memory chip selects
`define DM_WIDTH   8       // # of data mask bits
`define DQS_WIDTH  8       // # of DQS strobes
`define DQ_WIDTH   64      // # of data bits
`define ODT_WIDTH  1       // # of memory on-die term enables
`define ROW_WIDTH  13      // # of memory row and # of addr bits

`define NUM_PORTS  8

typedef 4 CACHE_LINE_WD_WIDTH;
typedef 7 SIZES_WIDTH; // to hold up to 64



// Section I:  THE INNER WRAPPER

// A:  The provided interface and associated definitions:

// Simple clock wrapper interface
interface ClkWrapper ;
   interface Clock clkOut ;
endinterface

typedef struct {
   TLMAddr#(`TLM_TYPES) addr;
   Bool rnw;
   UInt#(4) size;
   Bool rdModWr;
		} NPICmd#(`TLM_TYPE_PRMS) deriving(Bits, Eq);

typedef struct {
   TLMData#(`TLM_TYPES) wrData;
   TLMByteEn#(`TLM_TYPES) wrBE;
		} NPIWrArgs#(`TLM_TYPE_PRMS) deriving(Bits,Eq);

typedef struct {
   TLMData#(`TLM_TYPES) rdData;
   TLMCustom#(`TLM_TYPES) rdWdAddr;
		} NPIRdResult#(`TLM_TYPE_PRMS) deriving(Bits,Eq);

interface NPI_Port_Server#(`TLM_TYPE_PRMS);
   interface Put#(NPICmd#(`TLM_TYPES)) command;
   interface Put#(NPIWrArgs#(`TLM_TYPES)) writeData;
   interface Get#(NPIRdResult#(`TLM_TYPES)) readData;
endinterface

interface NPI_Port_Client#(`TLM_TYPE_PRMS);
   interface Get#(NPICmd#(`TLM_TYPES)) command;
   interface Get#(NPIWrArgs#(`TLM_TYPES)) writeData;
   interface Put#(NPIRdResult#(`TLM_TYPES)) readData;
endinterface

instance Connectable#(NPI_Port_Client#(`TLM_TYPES), NPI_Port_Server#(`TLM_TYPES));
   module mkConnection#(NPI_Port_Client#(`TLM_TYPES) c, NPI_Port_Server#(`TLM_TYPES) s)(Empty);
      mkConnection(c.command, s.command);
      mkConnection(c.writeData, s.writeData);
      mkConnection(c.readData, s.readData);
   endmodule
endinstance

instance Connectable#(NPI_Port_Server#(`TLM_TYPES), NPI_Port_Client#(`TLM_TYPES));
   module mkConnection#(NPI_Port_Server#(`TLM_TYPES) s, NPI_Port_Client#(`TLM_TYPES) c)(Empty);
      mkConnection(c, s);
   endmodule
endinstance

(* always_ready, always_enabled *)
interface DDR2_SDRAM;
   interface Vector#(`CLK_WIDTH, ClkWrapper) clk_p;
   interface Vector#(`CLK_WIDTH, ClkWrapper) clk_n;
   method    Bit#(`ROW_WIDTH)           a;
   method    Bit#(`BANK_WIDTH)          ba;
   method    Bit#(`CKE_WIDTH)           cke;
   method    Bit#(`CS_WIDTH)            cs_n;
   method    Bit#(1)                    ras_n;
   method    Bit#(1)                    cas_n;
   method    Bit#(1)                    we_n;
   method    Bit#(`DM_WIDTH)            dm;
   method    Bit#(`ODT_WIDTH)           odt;
   interface Inout#(Bit#(`DQS_WIDTH))   dqs;
   interface Inout#(Bit#(`DQS_WIDTH))   dqs_n;
   interface Inout#(Bit#(`DQ_WIDTH))    dq;
endinterface: DDR2_SDRAM


interface MPMC_NPI;
   interface Vector#(`NUM_PORTS, NPI_Port_Server#(`TLM_MPMC_TYPES)) ports;
   interface DDR2_SDRAM ddr2;
endinterface

// B: Importing the raw device:

// Interfaces:

`define PORT_IFC(NUM) \
   method Bool initDone``NUM``; \
   method Action addr``NUM``(TLMAddr#(`TLM_TYPES) x); \
   method Action rnw``NUM``(Bool x); \
   method Action size``NUM``(UInt#(4) x); \
   method Action rdModWr``NUM``(Bool x); \
   method Action addrReq``NUM``(Bool x); \
   method Bool addrAck``NUM``; \
   method Action wrData``NUM``(TLMData#(`TLM_TYPES) x); \
   method Action wrBE``NUM``(TLMByteEn#(`TLM_TYPES) x); \
   method Action wrPush``NUM``(Bool x); \
   method Action wrFlush``NUM``(Bool x); \
   method Bool wrEmpty``NUM``; \
   method Bool wrAlmostFull``NUM``; \
   method TLMData#(`TLM_TYPES) rdData``NUM``; \
   method TLMCustom#(`TLM_TYPES) rdWdAddr``NUM``; \
   method Action rdPop``NUM``(Bool x); \
   method Action rdFlush``NUM``(Bool x); \
   method Bool rdEmpty``NUM``; \
   method UInt#(2) rdLatency``NUM``;

`define DDR2_RAW \
   method    Bit#(`CLK_WIDTH)           clk_p; \
   method    Bit#(`CLK_WIDTH)           clk_n; \
   method    Bit#(`ROW_WIDTH)           a; \
   method    Bit#(`BANK_WIDTH)          ba; \
   method    Bit#(`CKE_WIDTH)           cke; \
   method    Bit#(`CS_WIDTH)            cs_n; \
   method    Bit#(1)                    ras_n; \
   method    Bit#(1)                    cas_n; \
   method    Bit#(1)                    we_n; \
   method    Bit#(`DM_WIDTH)            dm; \
   method    Bit#(`ODT_WIDTH)           odt; \
   interface Inout#(Bit#(`DQS_WIDTH))   dqs; \
   interface Inout#(Bit#(`DQS_WIDTH))   dqs_n; \
   interface Inout#(Bit#(`DQ_WIDTH))    dq;

`define DDR2_METHODS \
  method DDR2_Clk     clk_p; \
  method DDR2_Clk_n   clk_n; \
  method DDR2_CE      cke; \
  method DDR2_CS_n    cs_n; \
  method DDR2_ODT     odt; \
  method DDR2_RAS_n   ras_n; \
  method DDR2_CAS_n   cas_n; \
  method DDR2_WE_n    we_n; \
  method DDR2_BankAddr ba; \
  method DDR2_Addr    a; \
  method DDR2_DM      dm; \
  ifc_inout dq(DDR2_DQ); \
  ifc_inout dqs(DDR2_DQS); \
  ifc_inout dqs_n(DDR2_DQS_n);

`define DDR2_METHLIST \
clk_p, clk_n, cke, cs_n, odt, ras_n, cas_n, we_n, ba, a, dm

interface NPI_raw#(`TLM_TYPE_PRMS);
  `PORT_IFC(0)
  `PORT_IFC(1)
  `PORT_IFC(2)
  `PORT_IFC(3)
  `PORT_IFC(4)
  `PORT_IFC(5)
  `PORT_IFC(6)
  `PORT_IFC(7)
  `DDR2_RAW
endinterface

// Components of the 'import "BVI"' module:

`define METHODS(NUM) \
   method PIM``NUM``_InitDone initDone``NUM``; \
   method addr``NUM``(PIM``NUM``_Addr) enable((*inhigh*) ADDR``NUM``_EN); \
   method rnw``NUM``(PIM``NUM``_RNW) enable((*inhigh*) RNW``NUM``_EN); \
   method size``NUM``(PIM``NUM``_size) enable((*inhigh*) SIZE``NUM``_EN); \
   method rdModWr``NUM``(PIM``NUM``_RdModWr) enable((*inhigh*) RDMODWR``NUM``_EN); \
   method addrReq``NUM``(PIM``NUM``_AddrReq) enable((*inhigh*) ADDRREQ``NUM``_EN); \
   method PIM``NUM``_AddrAck addrAck``NUM``; \
   method wrData``NUM``(PIM``NUM``_WrFIFO_Data) enable((*inhigh*) WRDATA``NUM``_EN); \
   method wrBE``NUM``(PIM``NUM``_WrFIFO_BE) enable((*inhigh*) WRBE``NUM``_EN); \
   method wrPush``NUM``(PIM``NUM``_WrFIFO_Push) enable((*inhigh*) WRPUSH``NUM``_EN); \
   method wrFlush``NUM``(PIM``NUM``_WrFIFO_Flush) enable((*inhigh*) WRFLUSH``NUM``_EN); \
   method PIM``NUM``_WrFIFO_Empty wrEmpty``NUM``; \
   method PIM``NUM``_WrFIFO_AlmostFull wrAlmostFull``NUM``; \
   method PIM``NUM``_RdFIFO_Data rdData``NUM``; \
   method PIM``NUM``_RdFIFO_WdAddr rdWdAddr``NUM``; \
   method rdPop``NUM``(PIM``NUM``_RdFIFO_Pop) enable((*inhigh*) RDPOP``NUM``_EN); \
   method rdFlush``NUM``(PIM``NUM``_RdFIFO_Flush) enable((*inhigh*) RDFLUSH``NUM``_EN); \
   method PIM``NUM``_RdFIFO_Empty rdEmpty``NUM``; \
   method PIM``NUM``_RdFIFO_Latency rdLatency``NUM``;

`define METHLIST(NUM) \
    initDone``NUM``, addr``NUM``, rnw``NUM``, size``NUM``, rdModWr``NUM``,\
    addrReq``NUM``, addrAck``NUM``, wrData``NUM``, wrBE``NUM``, wrPush``NUM``,\
    wrFlush``NUM``, wrEmpty``NUM``, wrAlmostFull``NUM``, rdData``NUM``,\
    rdWdAddr``NUM``, rdPop``NUM``, rdFlush``NUM``, rdEmpty``NUM``, rdLatency``NUM

`define METHLISTS \
    (`METHLIST(0), \
     `METHLIST(1), \
     `METHLIST(2), \
     `METHLIST(3), \
     `METHLIST(4), \
     `METHLIST(5), \
     `METHLIST(6), \
     `METHLIST(7), \
     `DDR2_METHLIST)

import "BVI" rawMPMC =
module mkRawMPMC(NPI_raw#(`TLM_TYPES));
// Parameters:

// Methods:
   `METHODS(0)
   `METHODS(1)
   `METHODS(2)
   `METHODS(3)
   `METHODS(4)
   `METHODS(5)
   `METHODS(6)
   `METHODS(7)
   `DDR2_METHODS

// Schedule:
   schedule
   `METHLISTS
      CF
   `METHLISTS;
endmodule


// C: Vectorizing the NPI_raw interface:

(*always_ready, always_enabled*)
interface NPI_rawPort#(`TLM_TYPE_PRMS);
   method Bool initDone;
   method Action addr(TLMAddr#(`TLM_TYPES) x);
   method Action rnw(Bool x);
   method Action size(UInt#(4) x);
   method Action rdModWr(Bool x);
   method Action addrReq(Bool x);
   method Bool addrAck;
   method Action wrData(TLMData#(`TLM_TYPES) x);
   method Action wrBE(TLMByteEn#(`TLM_TYPES) x);
   method Action wrPush(Bool x);
   method Action wrFlush(Bool x);
   method Bool wrEmpty;
   method Bool wrAlmostFull;
   method TLMData#(`TLM_TYPES) rdData;
   method TLMCustom#(`TLM_TYPES) rdWdAddr;
   method Action rdPop(Bool x);
   method Action rdFlush(Bool x);
   method Bool rdEmpty;
   method UInt#(2) rdLatency;
endinterface

typedef Vector#(8, NPI_rawPort#(`TLM_TYPES)) NPI_Port_Servers#(`TLM_TYPE_PRMS);

`define CONNECT(METHOD,NUM) \
  method METHOD = raw.METHOD``NUM``;

`define SECTION(NUM) \
     let ifc``NUM`` = (interface NPI_rawPort;\
	`CONNECT(initDone,``NUM``) \
	`CONNECT(addr,``NUM``) \
	`CONNECT(rnw,``NUM``) \
	`CONNECT(size,``NUM``) \
	`CONNECT(rdModWr,``NUM``) \
	`CONNECT(addrReq,``NUM``) \
	`CONNECT(addrAck,``NUM``) \
	`CONNECT(wrData,``NUM``) \
	`CONNECT(wrBE,``NUM``) \
	`CONNECT(wrPush,``NUM``) \
	`CONNECT(wrFlush,``NUM``) \
	`CONNECT(wrEmpty,``NUM``) \
	`CONNECT(wrAlmostFull,``NUM``) \
	`CONNECT(rdData,``NUM``) \
	`CONNECT(rdWdAddr,``NUM``) \
	`CONNECT(rdPop,``NUM``) \
	`CONNECT(rdFlush,``NUM``) \
	`CONNECT(rdEmpty,``NUM``) \
	`CONNECT(rdLatency,``NUM``) \
		       endinterface);\
      v[``NUM``] = ifc``NUM``;

function NPI_Port_Servers#(`TLM_TYPES) vectorize(NPI_raw#(`TLM_TYPES) raw);
   NPI_Port_Servers#(`TLM_TYPES) v = newVector;
   `SECTION(0)
   `SECTION(1)
   `SECTION(2)
   `SECTION(3)
   `SECTION(4)
   `SECTION(5)
   `SECTION(6)
   `SECTION(7)
   return v;
endfunction

/*
function Clock extractClock ( ClkWrapper ifc );
   return ifc.clkOut ;
endfunction
*/

import "BVI"  bitToClock =
module bitToClock #( Bit#(1) clk ) (ClkWrapper);
   default_reset () ;
   default_clock clkin()  ;

   port CLKIN = clk ;
   output_clock clkOut (CLK);

   same_family( clkin, clkOut);
endmodule

module mkRamPart#(NPI_raw#(`TLM_TYPES) r)(DDR2_SDRAM);
   let cps  <- mapM (bitToClock, unpack(r.clk_p));
   let cns  <- mapM (bitToClock, unpack(r.clk_n));

   interface  clk_p = /*map (extractClock,*/ cps/*)*/;
   interface  clk_n = /*map (extractClock,*/ cns/*)*/;
   method    a = r.a;
   method    ba = r.ba;
   method    cke = r.cke;
   method    cs_n = r.cs_n;
   method    ras_n = r.ras_n;
   method    cas_n = r.cas_n;
   method    we_n = r.we_n;
   method    dm = r.dm;
   method    odt = r.odt;
   interface dqs = r.dqs;
   interface dqs_n = r.dqs_n;
   interface dq = r.dq;
endmodule

// D: Converting a raw port to a BSV NPI_Port interface:

module mkMPMCWrapper(NPI_rawPort#(`TLM_TYPES) n, NPI_Port_Server#(`TLM_TYPES) _)
   provisos(Bits#(TLMCustom#(`TLM_TYPES), _));
   // Commands:

   FIFOF#(NPICmd#(`TLM_TYPES)) cmdff <- mkBypassFIFOF;

   (*/*no_implicit_conditions,*/ fire_when_enabled*)
   rule xmit_cmd;
      let c = cmdff.first();
      n.addr(c.addr);
      n.rnw(c.rnw);
      n.size(c.size);
      n.rdModWr(c.rdModWr);
      n.addrReq(True);
   endrule
   
   (* preempts="xmit_cmd, xmit_null_cmd" *)
   rule xmit_null_cmd;
      n.addr(?);
      n.rnw(?);
      n.size(?);
      n.rdModWr(?);
      n.addrReq(False);
   endrule

   rule deq_cmd(n.addrAck);
      cmdff.deq();
   endrule

   // Write Data:

   FIFOF#(NPIWrArgs#(`TLM_TYPES)) wrdff <- mkBypassFIFOF;

   (*/*no_implicit_conditions,*/ fire_when_enabled*)
   rule xmit_wrdata;
      let x = wrdff.first();
      n.wrData(x.wrData);
      n.wrBE(x.wrBE);
      n.wrPush(True);
   endrule

   (* preempts = "xmit_wrdata, xmit_null_wrdata" *)
   rule xmit_null_wrdata;
      n.wrData(?);
      n.wrBE(?);
      n.wrPush(False);
   endrule

   rule deq_wrdata (n.initDone && !n.wrAlmostFull);
      wrdff.deq; // implicit condition
   endrule

   // Read Data:

   // Must ensure that no pop is started unless there is certainly room to
   // receive the result.
   //
   // Here we do the simpler version (latency == 1).

   FIFOF#(NPIRdResult#(`TLM_TYPES)) rddff <- mkBypassFIFOF;
   Reg#(Bool) didRead <- mkDReg(False);
   PulseWire dequeueing <- mkPulseWire;

   (*preempts="start_read, no_read"*)
   rule start_read(n.rdLatency==1 && !n.rdEmpty &&
		   (dequeueing || (rddff.notFull() && !didRead)));
      didRead <= True;
      n.rdPop(True);
   endrule

   rule no_read;
      n.rdPop(False);
   endrule

   rule finish_read(didRead);
      let x = NPIRdResult { rdData : n.rdData, rdWdAddr : n.rdWdAddr };
      rddff.enq(x);
   endrule

   rule cannot_read(n.rdLatency!=1);
      $error("read fifo latency should be 1 -- please adjust pipelining");
   endrule
   
   rule service_flush_methods;
      n.rdFlush(False);
      n.wrFlush(False);
   endrule

   // Interface:

   interface Put command = toPut(cmdff);
   interface Put writeData = toPut(wrdff);
   interface Get readData;
      method ActionValue#(NPIRdResult#(`TLM_TYPES)) get();
	 let x <- toGet(rddff).get();
	 dequeueing.send();
	 return x;
      endmethod
   endinterface
endmodule

(* synthesize *)
module mkMPMC_NPI(MPMC_NPI);
   NPI_raw#(`TLM_MPMC_TYPES) r <- mkRawMPMC;
   let ramPart <- mkRamPart(r);
   let portsPart <- mapM(mkMPMCWrapper, vectorize(r));

   interface ports = portsPart;
   interface ddr2 = ramPart;
endmodule


/*
(*synthesize*)
module mkMPMC(NPI);
   let rm <- mkRawMPMC;
   let mw <- mkMPMCWrapper(rm);
   return mw;
endmodule
*/

endpackage
