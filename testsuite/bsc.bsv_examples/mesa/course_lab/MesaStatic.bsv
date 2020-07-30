// The main module of the Mesa design: instantiates all the submodules and
// connects them up.

// In the hardware version, the submodules perform the following functions:
//
// VFF: Virtual Frame FIFO -- the frames arriving from the dta_in interface
// are written to memory, and the packet headers are copied to the header
// processing pipeline, where the several stages operate as follows.
//
// MIF: MAC Interface -- parses and performs (minimal) checks on the L2
// header; also parses and checks the IPv4 headers, extracting the IP
// destination address to pass to the LPM module.  When the LPM returns its
// results, the MIF uses them to build a routing header, which is passed to
// the DM module, along with a pointer to the location of the frame in the VFF
// memory. 
//
// LPM: Longest Prefix Match -- executes a destination address longest prefix
// match to determine an appropriate egress for the packet.  The result is a
// routing record containing the information required to build a routing
// header.  This information is passed back to the MIF.
//
// DM: Data Mover -- responsible for merging the routing header with its
// associated frame, and sending the resulting packet to the dta_out
// interface.
//
// In this transactional model most of these submodules are greatly simplified
// (for example, the packets' payloads are not handled at all, so there is no
// need to store them in external memory etc.).


// Import Library modules required:
import ClientServer::*;
import Connectable::*;
import GetPut::*;
import RAM::*;

// Import Mesa's submodules:
import MesaDefs::*;
import MesaIDefs::*;
import Mesa_Vff::*;
import Mesa_Dm::*;
import Mesa_Mif::*;

// This is the LPM module -- uncomment the one you want to use

//import MesaTxLpm::*;       // the transactional model
import MesaStaticLpm::*;   // the rigid synchronous pipeline
//import MesaFlexLpm::*;     // the flexible pipeline, with port replicator
//import MesaCircLpm::*;     // the circular pipeline

// The interface for the Mesa chip:
interface IMesa;
   method Put#(EthPacket) dta_in;
   method Get#(RhPacket) dta_out;
   method RAMclient#(SramAddr,SramData) dram;
endinterface

// The main module:
(* synthesize *)
module mkMesa(IMesa);
   // Instantiate the submodules:
   IVff vff();
   mkMesa_Vff the_vff(vff);
   
   IDm dm();
   mkMesa_Dm the_dm(dm);
   
   ILpm lpm();
   mkMesaLpm the_lpm(lpm);
   
   IMif mif();
   mkMesa_Mif the_mif(mif);

   // Connect them up:
   mkConnection(dm.vff, vff.dm);
   mkConnection(mif.notify, vff.notify);
   mkConnection(mif.dm, dm.mif);
   mkConnection(mif.lpm, lpm.mif);
   
   // This connection not used in this level of modeling
   // mkConnection(mif.vff, vff.mif);

   // The outer interface is formed by from the appropriate submodules'
   // subinterfaces: 
   interface dta_in =  vff.dta_in;
   interface dta_out = dm.dta_out;
   interface dram = lpm.ram;
endmodule: mkMesa


