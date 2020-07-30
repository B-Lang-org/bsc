package MesaTxLpm;

import RegFile::*;
import RegFile::*;
import Memory::*;
import LPMMemory::*;
import ClientServer::*;
import GetPut::*;
import FIFO::*;
import Connectable::*;
import RPC::*;
import Cocoon::*;

import MesaDefs::*;
import MesaIDefs::*;

typedef Wires#(SramAddr, SramData) LPMMemoryWires;
typedef  Stub#(SramAddr, SramData) LPMMemoryStub;

(* synthesize *)
module mkTheCocoon(LPMMemoryWires);
   let mem <- mkLPMMemory;
   let cocoon <- mkCocoon(mem);
   return cocoon;
endmodule

(* synthesize *)
module mkMesaTxLpm(ILpm);
   let cocoon <- mkTheCocoon;
   let ilpmwires <- mkMesaTxLpm0;
   match {.ilpm, .wires} = ilpmwires;

   mkConnection(cocoon, wires);
   return ilpm;
endmodule

typedef Tuple2#(ILpm, LPMMemoryWires) ILPM0;

 (* synthesize *)
module mkMesaTxLpm0(ILPM0);
   LPMMemoryStub stub <- mkStub;
   let sram = stub.mem;

   Reg#(LuTag) tagr <- mkRegU;
   Reg#(Bit#(8)) third_base <- mkRegU;
   Reg#(Maybe#(SramAddr)) pending <- mkReg(Invalid);
   
   FIFO#(Tuple2#(LuResponse, LuTag)) toMIF();
   mkFIFO the_toMIF(toMIF);

   

   rule further_reads (isValid(pending));
      let d32 = (sram.read)(validValue(pending));
      if (d32[31] == 1)
	 begin
	    toMIF.enq(tuple2({0,d32[30:0]}, tagr));
	    pending <= Invalid;
	 end
      else
	 pending <= tagged Valid (d32[20:0] + {0, third_base});
   endrule

   interface ILpm fst;
      interface Server mif;
	 interface Put request;
	    method put(x) if (!isValid(pending));
	       action
		  match {.ipa, .tag} = x;
		  let d32a = (sram.read)({0, ipa[31:16]});
		  if (d32a[31] == 1)
		     toMIF.enq(tuple2({0,d32a[30:0]}, tag));
		  
		  else
		     begin
			pending <= tagged Valid (d32a[20:0] + {0, ipa[15:8]});
			tagr <= tag;
			third_base <= ipa[7:0];
		     end
	       endaction
	    endmethod: put
	 endinterface: request
	 
	 interface Get response;
	    method get() ;
	       actionvalue
		  toMIF.deq;
		  return(toMIF.first);
	    endactionvalue
	    endmethod: get
	 endinterface: response
      endinterface: mif
      // In the transactional model, we don't need to define the interface to a real RAM:
      interface ram = ?;
   endinterface: fst

   interface snd = stub.cocoon;
      
endmodule


endpackage
