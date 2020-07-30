package MesaCircLpm;

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
// This version uses a circular pipeline, with one memory access each cycle
// for each circulating value.
//
// ----------------------------------------------------------------

// Required library packages:
import FIFO::*;
import RAM::*;
import ClientServer::*;
import CompletionBuffer::*;
import GetPut::*;
import CGetPut::*;
import List::*;
import Connectable::*;

// Other Mesa packages:
import MesaDefs::*;
import MesaIDefs::*;

// The type of results from the table lookup:

typedef union tagged {
    Bit#(21) Pointer;
    Bit#(31) Leaf;
} TableType deriving (Eq, Bits);

// The first lookup consumes the first 16 bits of the IP address.  The
// following type is for the remainder -- either two eight-bit chunks (after
// the first lookup) or just one (after the second):

typedef union tagged {
    Tuple2#(Bit#(8),Bit#(8)) L1;
    Bit#(8) L2;
    void L3;
} IP deriving (Eq, Bits);

// Latency is the total latency for the Lpm; this includes all steps in
// the process and the memory latency.  If latency is too low then the
// external ram will not be fully utilized. If the latency is too high
// then unnecessarily large FIFOs are created.

typedef 15 Latency;

// Longest prefix matching is done on several requests at the same time. A
// completion buffer ensures that the output is in the same order as the
// requests. The completion buffer also limits the number of requests worked
// on at the same time.

typedef Latency CompletionBufferSize;
typedef CBToken#(CompletionBufferSize) CompletionToken;

(* synthesize *)
module mkMesaLpm(ILpm);
   // registers for debugging purposes:
   Reg#(LuRequest) requestB32();
   mkRegU the_requestB32(requestB32);

   Reg#(LuTag) requestTag();
   mkRegU the_requestTag(requestTag);

   Reg#(LuResponse) responseB32();
   mkRegU the_responseB32(responseB32);

   Reg#(LuTag) responseTag();
   mkRegU the_responseTag(responseTag);

   // Technical detail: Latency is actually a numeric type.  We now define
   // an integer with corresponding value:
   Integer sz = valueOf(Latency);

   // the FIFOs for requests to and responses from the RAM:
   FIFO#(SramAddr) sramReq();
   mkSizedFIFO#(2) the_sramReq(sramReq);

   FIFO#(SramData) sramResp();
   mkSizedFIFO#(sz + 2) the_sramResp(sramResp);

   // The FIFO for input requests:
   FIFO#(Tuple2#(LuRequest, LuTag)) ififo();
   mkSizedFIFO#(sz) the_ififo(ififo);

   // The FIFO for work in progress:
   FIFO#(Tuple3#(IP, LuTag, CompletionToken)) fifo();
   mkSizedFIFO#(sz + 2) the_fifo(fifo);

   // The Completion Buffer, which holds completed results
   CompletionBuffer#(CompletionBufferSize, Tuple2#(LuResponse, LuTag)) completionBuffer();
   mkCompletionBuffer the_completionBuffer(completionBuffer);

   // All processing starts with a table lookup. This rule also claims a
   // completion token from the completion buffer:
   rule stage0;
      match {.ireq,.ilutag} = ififo.first;
      ififo.deq;
      let tag <- completionBuffer.reserve.get;

      // We send a request to the RAM, and also enqueue (for the next
      // stage) the remainder of the address, the lookup-tag and the
      // completion-buffer tag.  (Ln is the remainder after the nth
      // lookup).
      fifo.enq(tuple3(L1 (tuple2(ireq[15:8], ireq[7:0])), ilutag, tag));
      sramReq.enq(zeroExtend(ireq[31:16]));
   endrule: stage0

   // Processing stops if we found a Leaf.
   rule stage1_Leaf (unpack(sramResp.first) matches tagged Leaf (.v));
      sramResp.deq;
      let {ip,lutag,itag} = fifo.first;
      fifo.deq;
      completionBuffer.complete.put(tuple2(itag,tuple2(unpack({0,v}),lutag)));
   endrule: stage1_Leaf

   // If we found a pointer, a further lookup is necessary.  We also
   // enqueue the remainder of the address (Ln is the remainder after the
   // nth lookup).
   (* descending_urgency = "stage1_Pointer,stage0" *)
   rule stage1_Pointer (unpack(sramResp.first) matches tagged Pointer (.p));
      sramResp.deq;
      let {ip,lutag,itag} = fifo.first;
      fifo.deq;
      // nr: next remainder
      let nr = begin case (ip) matches
			tagged L1 {.b,.c} :  (L2 (c));
			tagged L2 {.c}    :  (L3);
			tagged L3         :  (?);  // never happens
		     endcase end;
      let addr = begin case (ip) matches
			  tagged L1 {.b,.c} :  (p + zeroExtend(b));
			  tagged L2 {.c}    :  (p + zeroExtend(c));
			  tagged L3         :  (?);  // never happens
		       endcase end;
      fifo.enq(tuple3(nr,lutag,itag));
      sramReq.enq(addr);
   endrule: stage1_Pointer

   // Finally we define the two interfaces:
   interface Server mif;
      interface Put request;
	 method put(x);
	    action
	       ififo.enq(x);
	       // record request for debugging purposes:
	       let {ipa,lutag} = x;
	       requestB32 <= ipa;
	       requestTag <= lutag;
	    endaction
	 endmethod: put
	 // or, apart from the debugging info:
	 // interface request = fifoToPut(ififo);
      endinterface: request
      interface Get  response;
	 method get() ;
	    actionvalue
	       let resp <- completionBuffer.drain.get();
	       // record response for debugging purposes:
	       let {r,t} = resp;
	       responseB32 <= r;
	       responseTag <= t;
	       return(resp);
	    endactionvalue
	 endmethod: get
	 // or, apart from the debugging info:
	 // interface response = fifoToGet(completionBuffer.drain);
      endinterface: response
   endinterface: mif

   interface Client ram;
      interface Get request;
	 method get();
	    actionvalue
	       let req = sramReq.first;
	       sramReq.deq;
	       return (Read (req));
	    endactionvalue
	 endmethod: get
      endinterface: request
      interface Put response = fifoToPut(sramResp);
   endinterface: ram
endmodule

endpackage
