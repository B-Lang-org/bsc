package MesaTxLpm;

// ----------------------------------------------------------------
//
// The LPM module is responsible for taking 32-bit IP addresses, looking up
// the destination (32-bit data) for each IP address in a table in an SRAM,
// and returning the destinations. 
//
// ----------------------------------------------------------------
//
// ILpm is the interface to the LPM module, containing two
// sub-interfaces: mif and ram.  It is defined in the interface definition
// package, MesaIDefs, imported above.
//
// ----------------------------------------------------------------
//
// The LPM module sits between two other blocks:
//   * the MIF (Media Interface)
//   * the SRAM
//
// The LPM receives requests from the MIF module by the method
//     mif.put (LuRequest, LuTag)
// and returns results (some cycles later) of the form (luResponse, luTag) by
// the method 
//     mif.get.
//
// The LPM sends addresses to the RAM by calling
//     ram.put(sramAddr)
// and receives result data (some cycles later) from the RAM by the method
//     ram.get
//
// ----------------------------------------------------------------
//
// The longest prefix match traverses a tree representation in memory. The
// first step is a table lookup, and after that it iterates if necessary until
// a leaf is reached.
//
// ----------------------------------------------------------------
//
// This is the simple transactional version of the Longest Prefix Match
// algorithm.  In this version the lookup table is stored locally, so the RAM
// interface described above is not used.
//
// ----------------------------------------------------------------

// Packages from the Library:
import RegFile::*;
import RegFile::*;
import RAM::*;
import ClientServer::*;
import GetPut::*;
import FIFO::*;
import Connectable::*;

// Other Mesa packages:
import MesaDefs::*;
import MesaIDefs::*;
import ShiftRegisters::*;

(* synthesize *)
module mkMesaLpm(ILpm);

   // For this model we instantiate the lookup table right here, instead of
   // holding it in RAM external to the whole design:
   RegFile#(SramAddr, SramData) sram();
   mkRegFileLoad#("SRAM.handbuilt", 0, 'h1fffff) the_sram(sram) ;
   
   // This function defines the lookup algorithm:
   function lookup(iput);
      let {ipa,tag} = iput;
      
      // first lookup:
      let d32a =  (sram.sub)({0, ipa[31:16]});
      
      // if it's a leaf, leave unchanged; otherwise lookup again:
      let d32b = d32a[31:31] == 1 ? {1, d32a[30:0]} : (sram.sub)(d32a[20:0] + {0, ipa[15:8]});
      
      // if it's a leaf, leave unchanged; otherwise lookup again:
      let d32c = d32b[31:31] == 1 ? {0, d32b[30:0]} : (sram.sub)(d32b[20:0] + {0, ipa[7:0]});
      
      // by now we must have an answer -- return it:
      return (tuple2(d32c, tag));
   endfunction

   // The rest of the Mesa transactional model expects the LPM module to have
   // some latency, and throughput suffers if it does not.  So we use a shift
   // FIFO to introduce some latency:
   Integer latency = 2;
   FIFO#(Tuple2#(LuResponse, LuTag)) toMIF();
   mkShiftFIFO#(latency) the_toMIF(toMIF);
   
   interface Server mif;
      interface Put request = fifoToPut(toMIF);
      interface Get response = fifoToGet(toMIF);
   endinterface: mif
   
   // In the transactional model, we don't need to define the interface to a real RAM:
   interface ram = ?;
endmodule

endpackage

