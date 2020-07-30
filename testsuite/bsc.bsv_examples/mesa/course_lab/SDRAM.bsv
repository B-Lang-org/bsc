// This package, adapted from the library, provideds a wrapper for external
// SDRAMs, converting their synchronous interface into one which observes the
// BSV protocol.  Note, however, that this wrapper contains only a small
// amount of FIFO storage, and read data items are dropped if the output FIFO
// is full; so the design still has to keep up with the memory's speed.

package SDRAM;

import FIFOF::*;
import ConfigReg::*;
import GetPut::*;
import ClientServer::*;
import RAM::*;

// These next definitions give the dimensions of the external RAM.  They could
// have been made parameters of the ExtSDRAM interface.

typedef 25 AddrSize;
typedef 32 DataSize;

interface ExtSDRAM;
   method Bool rd();
   method Bool wr();
   method Bit#(AddrSize) addr();
   method Bit#(DataSize) dIn();
   method Action dOut(Maybe#(Bit#(DataSize)) x1);
endinterface: ExtSDRAM

// This module provides a pair of interfaces: the interface to the external
// RAM, and the interface provided to the rest of the design.
module mkSDRAM(Tuple2#(ExtSDRAM, RAM#(adr, dta)))
   provisos (Bits#(adr, adrs),
             Add#(adrs, na, AddrSize),
             Add#(na, adrs, AddrSize),
             Bits#(dta, dtas),
             Add#(dtas, nd, DataSize),
             Add#(nd, dtas, DataSize),
             // this proviso should not be necessary
             Bits#(RAMreq#(Bit#(adrs), Bit#(dtas)), nr));

   // We use unguarded FIFOs: this allows us to ensure that the methods to the
   // extRAM have no implicit conditions and are therefore always enabled, but
   // it means that we have to be careful never to call the FIFO's methods
   // when their conditions for validity are not satisfied.

   // The FIFO for input requests from the design:
   FIFOF#(RAMreq#(Bit#(adrs), Bit#(dtas))) ififo();
   mkUGFIFOF theififo(ififo);

   // The FIFO for sending read results back to the design:
   FIFOF#(Bit#(dtas)) ofifo();
   mkUGFIFOF theofifo(ofifo);

   // This register holds the read-request flag for the external RAM:
   Reg#(Bool) doRD();
   mkConfigReg#(False) thedoRD(doRD);

   // This register holds the write-request flag for the external RAM:
   Reg#(Bool) doWR();
   mkConfigReg#(False) thedoWR(doWR);

   // This holds the address in external-RAM requests:
   Reg#(Bit#(adrs)) oAddr();
   mkConfigRegU theoAddr(oAddr);

   // This holds the data for external-RAM write requests:
   Reg#(Bit#(dtas)) oData();
   mkConfigRegU theoData(oData);

   // This function provides an Action to set the external RAM's parameter
   // registers for the next request, based on a request received from the
   // design: 
   function setupCycle(x);
      action
	 case (x) matches
            tagged Read {.a} :
               action
                  oAddr <= a;
                  doRD <= True;
                  doWR <= False;
               endaction
            tagged Write {.a,.d} :
               action
                  oAddr <= a;
                  oData <= d;
                  doRD <= False;
                  doWR <= True;
               endaction
         endcase
      endaction
   endfunction: setupCycle

   // A function to "bitify" a request from the design:
   function packReq(x);
      begin case (x) matches
               tagged Read {.a} :      return(Read (pack(a)));
               tagged Write {.a,.d} :  return(Write (tuple2(pack(a), pack(d))));
            endcase
      end
   endfunction: packReq

   // This Action sets up a new external RAM request if a request from the
   // design is present in the input queue:
   let newCycle =
   action
      setupCycle(ififo.first);
      ififo.deq;
   endaction;
   
   interface ExtSDRAM fst;
      method rd() ;   return (doRD);
      endmethod: rd
		    
      method wr() ;   return (doWR);
      endmethod: wr
		    
      method addr() ;   return (zeroExtend(oAddr));
      endmethod: addr
		    
      method dIn() ;   return (zeroExtend(oData));
      endmethod: dIn
		    
      method dOut(x);
         action
	    case (x) matches
               tagged Invalid :  noAction;
               tagged Valid {.d} :
		  if (ofifo.notFull)
		     (ofifo.enq)(truncate(d));
	    endcase
	    if (ififo.notEmpty)
	       newCycle;
	    else
               action
                  doRD <= False;
                  doWR <= False;
               endaction
         endaction
      endmethod: dOut
   endinterface: fst
   
   interface Server snd;
      interface Put request;
         method put(req) if (ififo.notFull) ;
	    action
               let preq =  packReq(req);
               ififo.enq(preq);
            endaction
         endmethod: put
      endinterface
      
      interface Get response;
         method get() if (ofifo.notEmpty) ;
	    actionvalue
               ofifo.deq;
               return(unpack(ofifo.first));
            endactionvalue
         endmethod: get
      endinterface
   endinterface: snd

endmodule: mkSDRAM

endpackage: SDRAM
