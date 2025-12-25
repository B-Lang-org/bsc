package BRAM ;

import BRAMCore ::*;
import ClientServer ::*;
import FIFOF :: *;
import DReg :: *;
import GetPut :: *;
import SpecialFIFOs :: *;

//  Export  section

// Types for the bram configuration data
export LoadFormat(..), BRAM_Configure(..);
export BRAMRequest(..), BRAMRequestBE(..);

// Interfaces
export BRAMServer   (..),   BRAMClient   (..) ;
export BRAMServerBE (..), BRAMClientBE (..) ;
export BRAM1Port   (..), BRAM2Port   (..) ;
export BRAM1PortBE (..), BRAM1PortBE8 (..), BRAM2PortBE (..) ;
export BRAM(..);

// Modules for export
export mkBRAM1Server;
export mkBRAM1ServerBE;

export mkBRAM2Server;
export mkBRAM2ServerBE;
export mkSyncBRAM2Server;
export mkSyncBRAM2ServerBE;

export mkBRAM, mkBRAMLoad, mkBRAM1, mkBRAM1Load, mkBRAM1BE, mkBRAM1BELoad, mkSyncBRAM, mkSyncBRAMLoad;

// Do we reexport some packages which are needed by users of this package?
export ClientServer::* ;
export GetPut::* ;

/////////////////////////////////////////////////////////////////////
// Structures for BRAM configuration
typedef struct {
                Integer      memorySize ;
                Integer      latency ;              // 1 or 2 can extend to 3
                LoadFormat   loadFormat;            // None, Hex or Binary
                Integer      outFIFODepth;
                Bool         allowWriteResponseBypass;
   } BRAM_Configure ;

typedef union tagged {
                      void None;
                      String Hex;
                      String Binary;
   } LoadFormat
deriving (Eq, Bits);

// An instance of DefaultValue for BRAM_Configure
// Example usage:
//  BRAM_Configure bramcfg = defaultValue ;
//               bramcfg.memorySize = 1024*32 ;
// let bram <- mkBRAM2Server (bramcfg) ;
instance DefaultValue #(BRAM_Configure);
   defaultValue = BRAM_Configure {
                                  memorySize         : 0
                                  ,latency           : 1 // No output reg
                                  ,outFIFODepth      : 3
                                  ,loadFormat        : None
                                  ,allowWriteResponseBypass : False
                                  };
endinstance


////////////////////////////////////
// Structures for requests
typedef struct {
                Bool write;
                Bool responseOnWrite;
                addr address;
                data datain;
                } BRAMRequest#(type addr, type data) deriving(Bits, Eq);

// Allowing for Byte enable signal
typedef struct {
                Bit#(n) writeen;
                Bool    responseOnWrite;
                addr    address;
                data    datain;
                } BRAMRequestBE#(type addr, type data, numeric type n) deriving (Bits, Eq);


// Define default values for the BRAMRequest{,BE} structures
instance DefaultValue#( BRAMRequest#(addr, data) )
   provisos (DefaultValue #(addr),
             DefaultValue #(data));
   defaultValue = BRAMRequest {write : False
                               ,responseOnWrite : True
                               ,address: defaultValue
                               ,datain:  defaultValue
                               };
endinstance

instance DefaultValue#( BRAMRequestBE#(addr, data, n) )
   provisos (DefaultValue #(addr),
             DefaultValue #(data));
   defaultValue = BRAMRequestBE {writeen : 0
                                 ,responseOnWrite : True
                                 ,address: defaultValue
                                 ,datain:  defaultValue
                                 };
endinstance

// Define Server and Client types for BRAM request
typedef Server#(BRAMRequest#(addr, data), data) BRAMServer#(type addr, type data);
typedef Client#(BRAMRequest#(addr, data), data) BRAMClient#(type addr, type data);

// with byte enables
typedef Server#(BRAMRequestBE#(addr, data, n), data) BRAMServerBE#(type addr, type data, numeric type n);
typedef Client#(BRAMRequestBE#(addr, data, n), data) BRAMClientBE#(type addr, type data, numeric type n);


// Top level interfaces for the BRAM server modules
interface BRAM1Port#(type addr, type data);
   interface BRAMServer#(addr, data) portA;
   (*always_ready*)
   method Action portAClear;
endinterface: BRAM1Port

interface BRAM1PortBE#(type addr, type data, numeric type n);
   interface BRAMServerBE#(addr, data, n) portA;
   (*always_ready*)
   method Action portAClear;
endinterface: BRAM1PortBE

// A version that assumes each byte is 8 bits.
typedef BRAM1PortBE#(addr, data, TDiv#(SizeOf#(data), 8)) BRAM1PortBE8#(type addr, type data);

interface BRAM2Port#(type addr, type data);
   interface BRAMServer#(addr, data) portA;
   interface BRAMServer#(addr, data) portB;
   (*always_ready*)
   method Action portAClear;
   (*always_ready*)
   method Action portBClear;
endinterface: BRAM2Port

typedef BRAM2Port BRAM;

interface BRAM2PortBE#(type addr, type data, numeric type n);
   interface BRAMServerBE#(addr, data, n) portA;
   interface BRAMServerBE#(addr, data, n) portB;
   (*always_ready*)
   method Action portAClear;
   (*always_ready*)
   method Action portBClear;
endinterface: BRAM2PortBE

//////////////////////////////////////////////////////////////////
// Various compatibility modules
(* deprecate = "Replaced by mkBRAM2Server" *)
module mkBRAM(Bool pipelined, BRAM2Port #(addr, data) ifc)
   provisos (
             Bits#(addr, addr_sz),
             Bits#(data, data_sz),
             Bounded#(addr)
            );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM2Server(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkBRAM2Server" *)
module mkBRAMLoad(Bool pipelined, String filename, BRAM2Port #(addr, data) ifc)
      provisos (
                Bits#(addr, addr_sz),
                Bits#(data, data_sz),
                Bounded#(addr)
               );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.loadFormat = tagged Hex filename;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM2Server(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkBRAM1Server" *)
module mkBRAM1(Bool pipelined, BRAM1Port #(addr, data) ifc)
   provisos (
             Bits#(addr, addr_sz),
             Bits#(data, data_sz),
             Bounded#(addr)
            );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM1Server(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkBRAM1Server" *)
module mkBRAM1Load(Bool pipelined, String filename, BRAM1Port #(addr, data) ifc)
      provisos (
                Bits#(addr, addr_sz),
                Bits#(data, data_sz)
               );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.loadFormat = tagged Hex filename;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM1Server(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkBRAM1ServerBE" *)
module mkBRAM1BE(Bool pipelined, BRAM1PortBE #(addr, data, n) ifc)
   provisos (
             Bits#(addr, addr_sz),
             Bits#(data, data_sz),
             Div#(data_sz, n, chunk_sz),
             Mul#(chunk_sz, n, data_sz)
            );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM1ServerBE(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkBRAM1ServerBE" *)
module mkBRAM1BELoad(Bool pipelined, String filename, BRAM1PortBE #(addr, data, n) ifc)
   provisos (
             Bits#(addr, addr_sz),
             Bits#(data, data_sz),
             Div#(data_sz, n, chunk_sz),
             Mul#(chunk_sz, n, data_sz)
            );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = pipelined ? 2:1 ;
   cfg.loadFormat = tagged Hex filename;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkBRAM1ServerBE(cfg);
   return _x;
endmodule

(* deprecate = "Replaced by mkSyncBRAM2Server" *)
module mkSyncBRAM#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB)(BRAM2Port#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = hasOutputRegister ? 2:1 ;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkSyncBRAM2Server(cfg, clkA, rstNA, clkB, rstNB );
   return _x;
endmodule

(* deprecate = "Replaced by mkSyncBRAM2Server" *)
module mkSyncBRAMLoad#(Bool hasOutputRegister, Clock clkA, Reset rstNA, Clock clkB, Reset rstNB, String filename)(BRAM2Port#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   BRAM_Configure cfg = defaultValue ;
   cfg.latency = hasOutputRegister ? 2:1 ;
   cfg.loadFormat = tagged Hex filename;
   cfg.allowWriteResponseBypass = False ;
   (*hide*)
   let _x <- mkSyncBRAM2Server(cfg, clkA, rstNA, clkB, rstNB );
   return _x;
endmodule

///////////////////////////////////////////////////////////////////
// Single Port Wrapper for various low-level BRAM
// Used to resolve BRAM_Configure information
// Not exported
module mkBRAM1Port #(BRAM_Configure cfg ) (BRAM_PORT #(addr, data) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   let latency = cfg.latency;
   let memSize = cfg.memorySize == 0 ? 2**valueOf(addr_sz) : cfg.memorySize ;
   let mod = ?;
   let errorLatency = error ("latency must be either 1 or 2") ;
   let errorFile    = error ("File name must not be empty") ;
   checkSizes( cfg, addr ' (?), "mkBRAM1Port" );

   Bool hasOutputPort = ((latency == 1) ? False:
                         (latency == 2) ? True :
                         errorLatency );

   case (cfg.loadFormat) matches
      tagged None:         mod = mkBRAMCore1(memSize, hasOutputPort );
      tagged Hex .file:    mod = mkBRAMCore1Load(memSize, hasOutputPort, file, False);
      tagged Binary .file: mod = mkBRAMCore1Load(memSize, hasOutputPort, file, True);
      default:             mod = error ("Invalid loadFormat in mkBRAM1Port");
   endcase
   (*hide*)
   let _i <- mod;
   return _i ;
endmodule

// Single Port Wrapper with Byte enables
// Used to resolve BRAM_Configure information
// Not exported
module mkBRAM1PortBE #(BRAM_Configure cfg ) (BRAM_PORT_BE #(addr, data, n) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );
   let latency = cfg.latency;
   let memSize = cfg.memorySize == 0 ? 2**valueOf(addr_sz) : cfg.memorySize ;
   let mod = ?;
   let errorLatency = error ("latency must be either 1 or 2") ;
   let errorFile    = error ("File name must not be empty") ;
   checkSizes( cfg, addr ' (?), "mkBRAM1PortBE" );

   Bool hasOutputPort = ((latency == 1) ? False:
                         (latency == 2) ? True :
                         errorLatency );

   case (cfg.loadFormat) matches
      tagged None:         mod = mkBRAMCore1BE(memSize, hasOutputPort );
      tagged Hex .file:    mod = mkBRAMCore1BELoad(memSize, hasOutputPort, file, False);
      tagged Binary .file: mod = mkBRAMCore1BELoad(memSize, hasOutputPort, file, True);
      default:             mod = error ("Invalid loadFormat in mkBRAM1PortBE");
   endcase

   (*hide*)
   let _i <- mod;
   return _i ;
endmodule


// Dual port version
// Used to resolve BRAM_Configure information
// Not exported
(* no_default_clock, no_default_reset *)
module mkSyncBRAM2Port #(
                         BRAM_Configure cfg,
                         Clock clkA, Reset rstNA,
                         Clock clkB, Reset rstNB
                        ) (BRAM_DUAL_PORT #(addr, data) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );
   let latency = cfg.latency;
   let memSize = cfg.memorySize == 0 ? 2**valueOf(addr_sz) : cfg.memorySize ;
   let mod = ?;
   let errorLatency = error ("latency must be either 1 or 2") ;
   let errorFile    = error ("File name must not be empty") ;
   checkSizes( cfg, addr ' (?), "mkSyncBRAM2Port" );

   Bool hasOutputPort = ((latency == 1) ? False:
                         (latency == 2) ? True :
                         errorLatency );

   case (cfg.loadFormat) matches
      tagged None:         mod = mkSyncBRAMCore2(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB );
      tagged Hex .file:    mod = mkSyncBRAMCore2Load(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB, file, False);
      tagged Binary .file: mod = mkSyncBRAMCore2Load(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB, file, True);
      default:             mod = error ("Invalid loadFormat in mkSyncBRAM2Port");
   endcase

   (*hide*)
   let _i <- mod;
   return _i ;
endmodule

(* no_default_clock, no_default_reset *)
module mkSyncBRAM2PortBE #(
                           BRAM_Configure cfg,
                           Clock clkA, Reset rstNA,
                           Clock clkB, Reset rstNB
                         ) (BRAM_DUAL_PORT_BE #(addr, data, n) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );
   let latency = cfg.latency;
   let memSize = cfg.memorySize == 0 ? 2**valueOf(addr_sz) : cfg.memorySize ;
   let mod = ?;
   let errorLatency = error ("latency must be either 1 or 2") ;
   let errorFile    = error ("File name must not be empty") ;
   checkSizes( cfg, addr ' (?), "mkSyncBRAM2PortBE" );

   Bool hasOutputPort = ((latency == 1) ? False:
                         (latency == 2) ? True :
                         errorLatency );

   case (cfg.loadFormat) matches
      tagged None:         mod = mkSyncBRAMCore2BE(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB );
      tagged Hex .file:    mod = mkSyncBRAMCore2BELoad(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB, file, False);
      tagged Binary .file: mod = mkSyncBRAMCore2BELoad(memSize, hasOutputPort, clkA, rstNA, clkB, rstNB, file, True);
      default:             mod = error ("Invalid loadFormat in mkSyncBRAM2PortBE");
   endcase

   (*hide*)
   let _i <- mod;
   return _i ;
endmodule


// type classes to allow generic operation on bram, requests and responses
// not exported
typeclass RequestToBRAM #(type bram_request_t, type bramifc_t);
   function Action     doRequest( bramifc_t ifc, bram_request_t req );
endtypeclass
typeclass RequestToResponse #(type bram_request_t);
   function Bool       responseRequired (bram_request_t req);
   function Bool       isWriteRequest   (bram_request_t req);
endtypeclass
typeclass BRAMToResponse #(type bramifc_t, type response_t);
   function ActionValue#(response_t)   getResponse ( bramifc_t ifc );
   function response_t                 readResponse ( bramifc_t ifc ); // paassive no state changes
endtypeclass


// Internal interface used for adapter module
interface ServerWithClear # (type req, type resp);
   interface Server#( req, resp) server ;
   (*always_ready*)
   method Action clear ;
endinterface


// mkBRAMAdapter
// This module contains the control logic to turn a BRAM into a Server --
// There is an output fifo, and logic to control its loading and to avoid
// its overflow.
// Not exported
module mkBRAMAdapter #(
                       BRAM_Configure cfg,
                       bramifc_t bram
                      ) (ServerWithClear#(bramreq_t, bramresp_t) )
   provisos(
            Bits #(bramresp_t, sresp),
            //  This module can be used with any interface and request/response type
            // which satisfy the following provisos.
            RequestToBRAM# (bramreq_t, bramifc_t),
            RequestToResponse# (bramreq_t),
            BRAMToResponse# (bramifc_t, bramresp_t)
           );

   // Output fifo and adapter to to creating a bypass fifo.
   FIFOF#(bramresp_t) outData <- mkSizedBypassFIFOF( cfg.outFIFODepth );

   // a counter is needed to track the conditions for safe requests
   SizedReg cnt <- mkSizedReg( cfg.outFIFODepth, 0 );
   Bool okToRequest = cnt.isLessThan ( cfg.outFIFODepth ) ;

   RWire#(Tuple2#(Bool,Bool)) writeWithResp <- mkRWire;

   // register to track the flow into the bram
   Reg#(Maybe#(Bool))  s1 <- mkDReg(tagged Invalid);
   Action clearShiftRegs = s1._write (tagged Invalid);
   Bool requestInFlight = isValid(s1);
   Maybe#(Bool) readReady = s1._read ;

   // additional latency requires additional register
   if ( cfg.latency == 2 ) begin
      Reg#(Maybe#(Bool)) s2 <- mkReg(Invalid);
      readReady = s2._read ;
      requestInFlight = requestInFlight || isValid(s2);

      rule passRequest (isValid(s1) || isValid(s2) );
         s2 <= s1;
      endrule
      clearShiftRegs = (action
                           clearShiftRegs ;
                           s2._write (tagged Invalid);
                        endaction);
   end
   else if (cfg.latency != 1) begin
      // Only latency 1 and 2 are supported
      errorM ("mkBRAMAdapter:  an unsupported latency has been specified:" +
              fromInteger(cfg.latency) +
              ".  Only BRAM Servers with latency 1 or 2 are supported." );
   end

   if (cfg.allowWriteResponseBypass) begin
      rule stageReadResponse (writeWithResp.wget matches tagged Valid .wr &&&
                              !tpl_1(wr) );
         s1 <= tagged Valid True;
         cnt.addA (+1);
      endrule

      rule stageWriteResponseBypass (writeWithResp.wget matches tagged Valid .wr &&&
                                     tpl_1(wr) &&& tpl_2(wr) &&& !requestInFlight );
         // Bypass the normal flow and just enqueue a garbage response
         // Use the data from the ram to avoid extra muxing
         bramresp_t d = unpack(0);
         outData.enq (d);
         cnt.addA (+1);
      endrule

      rule stageWriteResponse (writeWithResp.wget matches tagged Valid .wr &&&
                               tpl_1(wr) &&& tpl_2(wr) &&& requestInFlight );
         //  normal flow, responses are given in order
         s1 <= tagged Valid True ;
         cnt.addA (+1);
      endrule
   end
   else begin // NO writeResponseBypass.
      rule stageReadResponseAlways (writeWithResp.wget matches tagged Valid .wr);
         Bool responseNeeded = ! tpl_1(wr) || tpl_2 (wr);
         s1 <= tagged Valid (responseNeeded);
         if (responseNeeded)   cnt.addA (+1);
      endrule
   end

   // If there is data it need to go, drop it into the fifo
   rule moveToOutFIFO (readReady matches tagged Valid .respNeeded);
      if (respNeeded) begin
         bramresp_t d <- getResponse(bram);
         outData.enq(d);
      end
   endrule
   rule overRun (readReady matches tagged Valid .d &&&
                 ! outData.notFull );
      $display( "ERROR: %m: mkBRAMAdapter overrun" );
   endrule

   interface Server server ;
      interface Get response ;
         method ActionValue#(bramresp_t) get ;
            bramresp_t d = outData.first;
            outData.deq ;
            cnt.addB (-1) ;
            return d;
         endmethod
      endinterface
      interface Put request ;
         method Action put (bramreq_t din)  if (okToRequest);
            doRequest( bram, din );
            Bool isWrite = isWriteRequest (din);
            Bool responseNeeded = responseRequired (din);
            writeWithResp.wset (tuple2 (isWrite, responseNeeded));
         endmethod
      endinterface
   endinterface
   method Action clear ;
      outData.clear;
      cnt <= 0 ;
      clearShiftRegs ;
   endmethod
endmodule


// Instances to convert from BRAMRequest to BRAM
instance RequestToBRAM #( BRAMRequest#(addr, data), BRAM_PORT#(addr, data) );
   function Action doRequest (  BRAM_PORT#(addr, data) ifc,  BRAMRequest#(addr, data) req );
      action
         ifc.put ( req.write, req.address, req.datain );
      endaction
   endfunction
endinstance
instance RequestToResponse #( BRAMRequest#(addr, data) );
   function Bool responseRequired ( BRAMRequest#(addr, data)  req);
      return req.responseOnWrite;
   endfunction
   function Bool isWriteRequest   (BRAMRequest#(addr, data) req) ;
      return req.write ;
   endfunction

endinstance
instance BRAMToResponse #( BRAM_PORT#(addr, data), data );
   function ActionValue#(data) getResponse ( BRAM_PORT#(addr, data) ifc );
       return
       (actionvalue
           return ifc.read ;
        endactionvalue);
    endfunction
   function data readResponse ( BRAM_PORT#(addr, data) ifc );
           return ifc.read ;
    endfunction
endinstance

// Instances connecting BRAM to BRAMRequest with BE
instance RequestToBRAM #( BRAMRequestBE#(addr, data, n), BRAM_PORT_BE#(addr, data, n) );
   function Action doRequest (  BRAM_PORT_BE#(addr, data, n) ifc,  BRAMRequestBE#(addr, data, n) req );
      action
         ifc.put ( req.writeen, req.address, req.datain );
      endaction
   endfunction
endinstance
instance RequestToResponse #( BRAMRequestBE#(addr, data, n) );
   function Bool responseRequired ( BRAMRequestBE#(addr, data, n)  req);
      return req.responseOnWrite || (req.writeen == 0) ;
   endfunction
   function Bool isWriteRequest   (BRAMRequestBE#(addr, data, n) req) ;
      return req.writeen != 0  ;
   endfunction

endinstance
instance BRAMToResponse #( BRAM_PORT_BE#(addr, data, n), data );
   function ActionValue#(data) getResponse ( BRAM_PORT_BE#(addr, data, n) ifc );
       return
       (actionvalue
           return ifc.read ;
        endactionvalue);
    endfunction
   function data readResponse ( BRAM_PORT_BE#(addr, data, n) ifc );
      return ifc.read ;
    endfunction
endinstance


//////////////////////////////////////////////////

// mkBRAM1Server
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// Exported module
module mkBRAM1Server #( BRAM_Configure cfg ) (BRAM1Port #(addr, data) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkBRAM1Server" );

   BRAM_PORT #(addr, data)  memory <- mkBRAM1Port(cfg);
   ServerWithClear# (BRAMRequest#(addr, data), data
                     ) serverAdapter <- mkBRAMAdapter ( cfg, memory );
   interface BRAMServer portA = serverAdapter.server ;
   method Action portAClear = serverAdapter.clear ;
endmodule

// mkBRAM1Server
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// With byte enable
// Exported module
module mkBRAM1ServerBE #( BRAM_Configure cfg ) (BRAM1PortBE #(addr, data, n) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkBRAM1ServerBE" );

   BRAM_PORT_BE #(addr, data, n)  memory <- mkBRAM1PortBE(cfg);
   ServerWithClear# (BRAMRequestBE#(addr, data, n), data
                     ) serverAdapter <- mkBRAMAdapter ( cfg, memory );
   interface BRAMServer portA = serverAdapter.server ;
   method Action portAClear = serverAdapter.clear ;
endmodule


// mkBRAM2Server  Dual ported
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// Exported module
module mkBRAM2Server #( BRAM_Configure cfg ) (BRAM2Port #(addr, data) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkBRAM2Server" );

   Clock clk <- exposeCurrentClock ;
   Reset rst <- exposeCurrentReset ;
   BRAM_DUAL_PORT #(addr, data)  memory <- mkSyncBRAM2Port(cfg, clk, rst, clk, rst);

   ServerWithClear# (BRAMRequest#(addr, data), data
                     ) serverAdapterA <- mkBRAMAdapter ( cfg, memory.a );
   ServerWithClear# (BRAMRequest#(addr, data), data
                    ) serverAdapterB <- mkBRAMAdapter ( cfg, memory.b );

   interface BRAMServer portA = serverAdapterA.server ;
   method Action portAClear = serverAdapterA.clear ;

   interface BRAMServer portB = serverAdapterB.server ;
   method Action portBClear = serverAdapterB.clear ;
endmodule


// mkBRAM2ServerBE  Dual ported
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// With byte enables
// Exported module
module mkBRAM2ServerBE #( BRAM_Configure cfg ) (BRAM2PortBE #(addr, data, n) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkBRAM2ServerBE" );

   Clock clk <- exposeCurrentClock ;
   Reset rst <- exposeCurrentReset ;
   BRAM_DUAL_PORT_BE #(addr, data, n)  memory <- mkSyncBRAM2PortBE(cfg, clk, rst, clk, rst);

   ServerWithClear# (BRAMRequestBE#(addr, data, n), data
                     ) serverAdapterA <- mkBRAMAdapter ( cfg, memory.a );
   ServerWithClear# (BRAMRequestBE#(addr, data, n), data
                    ) serverAdapterB <- mkBRAMAdapter ( cfg, memory.b );

   interface BRAMServer portA = serverAdapterA.server ;
   method Action portAClear = serverAdapterA.clear ;

   interface BRAMServer portB = serverAdapterB.server ;
   method Action portBClear = serverAdapterB.clear ;
endmodule


// mkSyncBRAM2Server   Dual ported  2 clocks
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// Exported module
(* no_default_clock, no_default_reset *)
module mkSyncBRAM2Server #(
                           BRAM_Configure cfg,
                           Clock clkA, Reset rstNA,
                           Clock clkB, Reset rstNB
                          ) (BRAM2Port #(addr, data) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkSyncBRAM2Server" );
   BRAM_DUAL_PORT #(addr, data)  memory <- mkSyncBRAM2Port(cfg, clkA, rstNA, clkB, rstNB);

   ServerWithClear# (BRAMRequest#(addr, data), data
                     ) serverAdapterA <- mkBRAMAdapter ( cfg, memory.a, clocked_by clkA, reset_by rstNA );
   ServerWithClear# (BRAMRequest#(addr, data), data
                    ) serverAdapterB <- mkBRAMAdapter ( cfg, memory.b, clocked_by clkB, reset_by rstNB );

   interface BRAMServer portA = serverAdapterA.server ;
   method Action portAClear = serverAdapterA.clear ;

   interface BRAMServer portB = serverAdapterB.server ;
   method Action portBClear = serverAdapterB.clear ;
endmodule

// mkSyncBRAM2ServerBE   Dual ported  2 clocks
// This module wraps the BRAM module with a mkBRAM Adapter to give a BRAM Server
// With byte enables
// Exported module
(* no_default_clock, no_default_reset *)
module mkSyncBRAM2ServerBE #(
                             BRAM_Configure cfg,
                             Clock clkA, Reset rstNA,
                             Clock clkB, Reset rstNB
                            ) (BRAM2PortBE #(addr, data, n) )
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   checkSizes( cfg, addr ' (?), "mkSyncBRAM2Server" );
   BRAM_DUAL_PORT_BE #(addr, data, n)  memory <- mkSyncBRAM2PortBE(cfg, clkA, rstNA, clkB, rstNB);

   ServerWithClear# (BRAMRequestBE#(addr, data, n), data
                     ) serverAdapterA <- mkBRAMAdapter ( cfg, memory.a, clocked_by clkA, reset_by rstNA );
   ServerWithClear# (BRAMRequestBE#(addr, data, n), data
                    ) serverAdapterB <- mkBRAMAdapter ( cfg, memory.b, clocked_by clkB, reset_by rstNB );

   interface BRAMServer portA = serverAdapterA.server ;
   method Action portAClear = serverAdapterA.clear ;

   interface BRAMServer portB = serverAdapterB.server ;
   method Action portBClear = serverAdapterB.clear ;
endmodule


module checkSizes (BRAM_Configure cfg, addr_t addr, String modName, Empty ifc)
   provisos( Bits#(addr_t, addr_sz) );

   if (cfg.memorySize > (2 ** valueOf(addr_sz))) begin
      addr_t xx = ?;
      errorM ("The memory size for " + modName + " module is greater than the range of the address type. " +
              "\nAddress type: " + printType (typeOf(xx)) +
              ", Addressable range: " + integerToString(2**valueOf(addr_sz)) +
              ", memory size: " + integerToString(cfg.memorySize) ) ;
   end

endmodule

//////////////////////////////////////////////////////////////////////////////////
// SizedReg allow an elaboration time argument to determine the register width.
// However, the method are limited to compile time arguments.
// This interface allows a hard set,  2 concurrent add ports, and various compare
// value methods.
//Not exported
interface SizedReg ;
   method Action _write (Integer i);
   method Action addA (Integer i);
   method Action addB (Integer d);
   method Bool isLessThan (Integer i);
   method Bool isGreaterThan (Integer i);
   method Bool isEqualTo (Integer i);
endinterface

//Not exported
module mkSizedReg (Integer maxVal, Integer initialVal, SizedReg ifc);
   SizedReg _ifc = ? ;
   if (maxVal < 2)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(2) '(fromInteger(initialVal)) );
   else if (maxVal < 4)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(3) '(fromInteger(initialVal)) );
   else if (maxVal < 8)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(4) '(fromInteger(initialVal)) );
   else if (maxVal < 16)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(5) '(fromInteger(initialVal)) );
   else if (maxVal < 32)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(6) '(fromInteger(initialVal)) );
   else if (maxVal < 64)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(7) '(fromInteger(initialVal)) );
   else if (maxVal < 128)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(8) '(fromInteger(initialVal)) );
   else if (maxVal < 256)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(9) '(fromInteger(initialVal)) );
   else if (maxVal < 512)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(10) '(fromInteger(initialVal)) );
   else if (maxVal < 1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(11) '(fromInteger(initialVal)) );
   else if (maxVal < 2*1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(12) '(fromInteger(initialVal)) );
   else if (maxVal < 4*1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(13) '(fromInteger(initialVal)) );
   else if (maxVal < 8*1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(14) '(fromInteger(initialVal)) );
   else if (maxVal < 16*1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(15) '(fromInteger(initialVal)) );
   else if (maxVal < 32*1024)
      (*hide*)
      _ifc <- mkSizedRegInt(Int#(16) '(fromInteger(initialVal)) );
   else
      _ifc = error ("Sized Register is too big: " + fromInteger (maxVal) );
   return _ifc;
endmodule

//Not exported
// scheduling is should be forced so that (read, is*) SB (addA, addB) SB  write
module mkSizedRegInt (a init, SizedReg ifc)
   provisos (Bits#(a,sa),
             Arith#(a),
             Eq#(a),
             Ord#(a) );

   (*hide*)
   Reg#(a) _cnt <- mkReg(init);
   (*hide*)
   RWire#(a)  _adda <- mkRWire ;
   (*hide*)
   RWire#(a)  _addb <- mkRWire ;
   (*hide*)
   RWire#(a)  _fwrite <- mkRWire ;

   rule finalAdd ( isValid(_adda.wget) || isValid (_addb.wget) || isValid(_fwrite.wget) ) ;
      if (_fwrite.wget matches tagged Valid .w) begin
         _cnt <= w;
      end
      else begin
         a va = fromMaybe (0, _adda.wget);
         a vb = fromMaybe (0, _addb.wget);
         _cnt <= _cnt + va + vb ;
      end
   endrule

   method Action _write (Integer i);
      _fwrite.wset (fromInteger(i));
   endmethod
   method Action addA (Integer i);
      _adda.wset (fromInteger(i));
   endmethod
   method Action addB (Integer i);
      _addb.wset (fromInteger(i));
   endmethod
   method Bool isLessThan (Integer i) ;
      return _cnt < fromInteger (i);
   endmethod
   method Bool isGreaterThan (Integer i) ;
      return _cnt > fromInteger (i);
   endmethod
   method Bool isEqualTo (Integer i) ;
      return _cnt == fromInteger (i);
   endmethod
endmodule

endpackage
