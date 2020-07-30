package MesaFlexLpm;

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
// The longest prefix match traverses a tree representation in  memory. The
// first step is a table lookup, and after that it iterates if necessary until
// a leaf is reached. 
//
// ----------------------------------------------------------------
//
// The module is pipelined, i.e., IP addresses stream in, and results stream
// out (after some latency).  Results are returned in the same order as
// requests. 
//
// The SRAM is also pipelined: addresses stream in, and data stream out
// (after some latency).  It can accept addresses and deliver data on every
// cycle.
//
// Performance metric: as long as IP lookup requests are available, the LPM
// module must keep the SRAM 100% utilized, i.e., it should issue a request
// into the SRAM on every cycle. 
//
// ----------------------------------------------------------------
//
// This version uses a "flexible" linear pipeline.  Each stage has its own
// port to the SRAM, produced by a server replicator, which it uses if
// necessary; otherwise it passes the result, completed at an earlier stage,
// along the pipe with no further processing.
//
// ----------------------------------------------------------------

// Required library packages:
import RAM::*;
import ClientServer::*;
import GetPut::*;
import FIFO::*;
import RegFile::*;
import List::*;

// Other Mesa packages:
import Replicator::*;
import MesaDefs::*;
import MesaIDefs::*;

// The type of results from the table lookup:
typedef union tagged {
    Bit#(21) Pointer;
    Bit#(31) Leaf;
} TableType deriving (Eq, Bits);

(* synthesize *)
module mkMesaLpm(ILpm);
   // max is the size of each FIFO in the pipeline.  If it is too low, there
   // may be bottlenecks when items mount up at a particular stage; if it is
   // too high the FIFOs will be unnecessarily large.
   let max =  8;
   // latency is the latency of the SRAM.  If this number is too low, the
   // memory will not be fully utilized; if too high, the replicator will
   // consume unnecessary amounts of storage.
   let latency = 8;

   // The ROM replicator:
   ClientServer#(RAMreq#(SramAddr,SramData), SramData) cs();
   mkRequestResponseBuffer the_cs(cs);
   match {.c,.s} = cs;
   Tuple3#(Server#(RAMreq#(SramAddr,SramData), SramData),
	   Server#(RAMreq#(SramAddr,SramData), SramData),
	   Server#(RAMreq#(SramAddr,SramData), SramData)) srams();
   mk3Servers#(latency) the_srams(s, srams);
   match {.sram0, .sram1, .sram2} = srams;

   // The FIFO for incoming requests:
   FIFO#(Tuple2#(LuRequest, LuTag)) ififo();
   mkSizedFIFO#(4) the_ififo(ififo);

   // The intermediate FIFOs:
   FIFO#(Tuple3#(Bit#(8), Bit#(8), LuTag)) fifo0();
   mkSizedFIFO#(max) the_fifo0(fifo0);
   
   FIFO#(Tuple3#(Maybe#(LuResponse), Bit#(8), LuTag)) fifo1();
   mkSizedFIFO#(max) the_fifo1(fifo1);
   
   FIFO#(Tuple2#(Maybe#(LuResponse), LuTag)) fifo2();
   mkSizedFIFO#(max) the_fifo2(fifo2);

   // The output FIFO:
   FIFO#(Tuple2#(LuResponse, LuTag)) ofifo();
   mkSizedFIFO#(4) the_ofifo(ofifo);
   
   // All processing starts with a table lookup. We send a request to the RAM,
   // and also enqueue (for the next stage) the remainder of the address and
   // the lookup-tag.
   rule stage0;
      let x = ififo.first;
      match {.ireq, .tag} = x;
      ififo.deq;
      
      sram0.request.put(Read(zeroExtend(ireq[31:16])));
      (fifo0.enq)(tuple3(ireq[15:8], ireq[7:0], tag));
   endrule: stage0

   // This rule handles the result of the first lookup.
   rule stage1;
      let x <- sram0.response.get();
      match {.a2,.a3,.tag} = fifo0.first;
      fifo0.deq;
      
      case (unpack(x)) matches
	 tagged Leaf .v:
	    // A leaf has been reached, so no further lookups are needed.  We
	    // send the result, with the tag, along the pipe.
	    fifo1.enq(tuple3(Valid (zeroExtend(v)), a3, tag));
	 tagged Pointer .a:
	    // No leaf, so another lookup is required.  We enqueue the
	    // relevant address, and send the remainder (with the tag) down
	    // the pipe.
	    begin
	       sram1.request.put(Read(a + zeroExtend(a2)));
	       fifo1.enq(tuple3(Invalid, a3, tag));
	    end
      endcase
   endrule: stage1

   // This rule for the next stage handles the case where a further lookup was
   // not required, so there is no result from the RAM to await.  We just pass
   // the result on.
   rule stage2_NoRAM (fifo1.first matches {tagged Valid .v, .a3, .tag});
      // TASK: write this rule.
   endrule: stage2_NoRAM

   // This rule handles the case where a second lookup was required.  It deals
   // with the result from the RAM in a way similar to stage 1.
   rule stage2_RAM (fifo1.first matches {tagged Invalid, .a3, .tag});
      let x <- sram1.response.get();
      fifo1.deq;
      
      case (unpack(x)) matches
	 tagged Leaf .v:
	    fifo2.enq(tuple2(Valid (zeroExtend(v)), tag));
	 tagged Pointer .a:
	    begin
	       // TASK: write this part.
	    end
      endcase
   endrule: stage2_RAM

   // The next two rules handle the third stage in the same way.
   rule stage3_NoRAM (fifo2.first matches {tagged Valid .v, .tag});
      // TASK: write this rule
   endrule: stage3_NoRAM
   
   rule stage3_RAM (fifo2.first matches {tagged Invalid, .tag});
      let x <- sram2.response.get();
      fifo2.deq;
      
      case (unpack(x)) matches
	 tagged Leaf .v:
	    ofifo.enq(tuple2(zeroExtend(v), tag));
	 tagged Pointer .a:
	    // This case should never happen (it indicates an error in the
	    // lookup table); we treat the pointer as though it was a leaf.
	    ofifo.enq(tuple2(zeroExtend(a), tag));
      endcase
   endrule: stage3_RAM

   // The MIF interface is formed from the input and output FIFOs:
   interface Server mif;
      interface Put request = fifoToPut(ififo);
      interface Get response = ?; // TASK: complete this definition.
   endinterface: mif

   // The RAM interface is the client corresponding to the replicated server
   // above:
   interface Client ram = ?; // TASK: complete this definition.
endmodule

endpackage: MesaFlexLpm

/*
 TASK:
 When this code is working, investigate how its performance (throughput)
 depends on the values of max and latency, defined above (note that although
 they have the same values above, they are not closely dependent on each
 other).
 
 Regrettably, perhaps, we have not yet constructed a maximally pathological
 set of test data to show the worst cases of the effect of the values of these
 parameters on the design's performance.  What properties would such a data
 set need to have?
*/
