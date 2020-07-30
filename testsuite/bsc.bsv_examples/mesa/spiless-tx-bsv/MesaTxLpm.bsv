package MesaTxLpm;

import RegFile::*;
import RegFile::*;
import RAM::*; /* qualified */
import ClientServer::*;
import GetPut::*;
import FIFO::*;

import MesaDefs::*;
import MesaIDefs::*;


(* synthesize *)
module mkMesaTxLpm(ILpm);

    RegFile#(SramAddr, SramData) sram();
   mkRegFileLoad#("SRAM.handbuilt", 0, 'h1fffff) the_sram(sram) ;
//   mkRegFile#(0, maxBound) the_sram(sram);

   // This function defines the lookup algorithm:
   function lookup(iput);
      let {ipa,tag} = iput;
      // first lookup:
      let d32a =  (sram.sub)({0, ipa[31:16]});
      // if it's a leaf, leave unchanged, otherwise lookup again:
      let d32b = d32a[31:31] == 1 ? {1, d32a[30:0]} : (sram.sub)(d32a[20:0] + {0, ipa[15:8]});
      // if it's a leaf, leave unchanged, otherwise lookup again:
      let d32c = d32b[31:31] == 1 ? {0, d32b[30:0]} : (sram.sub)(d32b[20:0] + {0, ipa[7:0]});
      // by now we must have an answer -- return it:
      return (tuple2(d32c, tag));
   endfunction
   
   FIFO#(Tuple2#(LuResponse, LuTag)) toMIF();
   mkFIFO the_toMIF(toMIF);
   
   interface Server mif;
      interface Put request;
	 method put(x);
	    action
	       toMIF.enq(lookup(x));
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

endmodule

endpackage

