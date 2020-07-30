package MesaStaticLpm;

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
// This version uses a static allocation of memory slots.  Each packet is
// allocated three accesses of the memory (whether it needs them or not).  The
// metric set out above is therefore not satisfied.  It also assumes that the
// MIF will be ready to absorb the result as soon as it appears: if it is not
// absorbed as soon as it appears at the end of the pipeline it is lost
// forever, as there is no means for stopping the flow.
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
import MesaDefs::*;
import MesaIDefs::*;
import ShiftRegisters::*;

typedef union tagged {
    Bit#(21) Pointer;
    Bit#(31) Leaf;
} TableType deriving (Eq, Bits);

// ----------------------------------------------------------------
//
// The first lookup consumes the first 16 bits of the IP address.  The
// following type is for the remainder: either two eight-bit chunks (after the
// first lookup) or just one (after the second).
//
// ----------------------------------------------------------------

typedef union tagged {
   Tuple3#(Bit#(16),Bit#(8),Bit#(8)) L1;
   Tuple2#(Bit#(21),Bit#(8)) L2;
   Bit#(21) L3;
   LuResponse D;
} IP deriving (Eq, Bits);


typedef Bit#(3) SlotTag;
typedef Bit#(3) Count;

typedef struct {
   SlotTag tag;
   Reg#(Bool) used;
   Reg#(LuTag) lutag;
   Reg#(IP) lu;
   Reg#(Count) count;
} Slot;

(* synthesize *)
module mkMesaLpm(ILpm);
   // The number of memory accesses required:
   let cycles =  3;
   // The latency of the memory (and associated wrapper).  This must be
   // exactly right, or requests and responses will not match up.
   let latency =  6;

   // This register holds the next "job" to be processed by the RAM.  The RAM
   // interface method reads it to construct its next request, and it also
   // gets fed into the shift register below, so that it can be matched up
   // again with the result when it returns from the memory.
   Reg#(Maybe#(Tuple3#(Count, IP, LuTag))) inputReg();
   mkReg#(Invalid) the_inputReg(inputReg);

   // This register stores a value derived from the result from the RAM and
   // the output from the shift register.  It may or may not be a final
   // result: it is read by the MIF interface Get method, which becomes ready
   // if this register does contain a final result.
   Reg#(Maybe#(Tuple3#(Count, IP, LuTag))) outputReg();
   mkReg#(Invalid) the_outputReg(outputReg);

   // This shift register holds the extra information belonging to requests
   // awaiting responses from the RAM.  Requests circulate round this register
   // the number of times specified by "cycles" above.  The length is
   // (latency-1) because the "inputReg" above is also in the ring.
   ShiftReg#(Tuple3#(Count, IP, LuTag)) shift();
   mkShifter#(latency - 1) the_shift(shift);
   
   // This RWire holds requests coming from the MIF interface: they will be
   // processed by a rule firing "later" in the same clock cycle.
   RWire#(Tuple2#(LuRequest, LuTag)) ins();
   mkRWire the_ins(ins);
   
   // This RWire holds results returning from the RAM interface: they will be
   // processed by a rule firing "later" in the same clock cycle.
   RWire#(SramData) rep();
   mkRWire the_rep(rep);

   // This function is used to examine the slot emerging from the shift
   // register, to tell whether it is vacant; if so, a new request can be
   // entertained.  The slot is vacant either if it is a bubble, or if it
   // contains a "job" which has reached its maximum number of cycles and is
   // about to be output.
   function Bool inReady(Maybe#(Tuple3#(Count, IP, LuTag)) x);
      case (x) matches
	 tagged Invalid:         return (True);
	 tagged Valid {.c,.*,.*}: return (c == cycles);
      endcase
   endfunction: inReady

   // This function is used to tell whether the contents of outputReg are a
   // valid final result which can be sent back to the MIF.  This is the case
   // if the value contains data ("tagged D") which has circulated for the
   // maximum number of cycles.
   function Bool outputReady(Maybe#(Tuple3#(Count, IP, LuTag)) x);
      case (x) matches
	 tagged Valid {.c,(tagged D {.*}),.*}: return (c == cycles);
	 default:                             return (False);
      endcase
   endfunction: outputReady

   // This function is used to turn the contents of outputReg into a result
   // for sending to the MIF.  The case statement is not exhaustive, as the
   // function is used only when the value satisfies outputReady above.
   function Tuple2#(LuResponse, LuTag) getOutput(Maybe#(Tuple3#(Count, IP, LuTag)) x);
      case (x) matches
	 tagged Valid {.c,(tagged D {.v}),.tag}: return (tuple2(zeroExtend(v), tag));
      endcase
   endfunction: getOutput

   // This function tells whether the contents of inputReg are such that a new
   // request needs to be made to the RAM.  There is no need if the register
   // contains either a final result or a bubble.
   function Bool makeReq(Maybe#(Tuple3#(Count, IP, LuTag)) x);
      case (x) matches
	 tagged Valid {.*,(tagged D {.*}),.*}: return (False);
	 tagged Invalid:                      return (False);
	 default:                             return (True);
      endcase
   endfunction: makeReq

   // This rule does all the processing.  It must fire on every cycle; so
   // attributes are specified to make the compiler check that it will.
   (* fire_when_enabled, no_implicit_conditions *)
   rule doThings (True);
      // The contents of inputReg are moved to the shift register, causing the
      // ring to circulate.
      shift.sin(inputReg);

      // The next contents of outputReg are computed.
      let newOut =
         begin
	    case (rep.wget) matches
	       tagged Valid .wg:
		  // The memory has returned a result: we pattern-match on a
		  // pair consisting of the output from the shift register and
		  // the memory result:
		  case (tuple2(shift.sout, unpack(wg))) matches

		     // The shift register has returned a bubble.  No output:
		     {tagged Invalid,.*} :  (Invalid);

		     // The memory has returned a leaf node.  Compute a
		     // result.  Increment the cycle count and send on.
		     {tagged Valid {.n,.*,.t}, tagged Leaf .v} :  
			       (Valid (tuple3(n + 1, D (zeroExtend(v)), t)));

		     // The memory has not returned a leaf, but we have used
		     // up all the address.  This indicates an error in the
		     // lookup table.  But for now we treat the pointer as a
		     // leaf: 
		     {tagged Valid {.n,tagged L3 .*,.t}, tagged Pointer .p} :
			       (Valid (tuple3(n + 1, D (zeroExtend(p)), t)));

		     // The next two cases handle a non-leaf node from the
		     // memory, used together with the next part of the
		     // address to form the next lookup request.
		     {tagged Valid {.n,tagged L2 {.*,.b},.t}, tagged Pointer .p} : 
			       (Valid (tuple3(n + 1, L3 (p + zeroExtend(b)), t)));
		     {tagged Valid {.n,tagged L1 {.*,.b,.c},.t}, tagged Pointer .p} : 
			       (Valid (tuple3(n + 1, L2 (tuple2(p + zeroExtend(b), c)), t)));
		  endcase
	       tagged Invalid:
		  // Invalid back from the memory:
		  case (shift.sout) matches
		     // Bubble: send on.
		     tagged Invalid :  (Invalid);
		     // Non-bubble: send on, incrementing the cycle count.
		     tagged Valid {.n,.v,.t} :  (Valid (tuple3(n + 1, v, t)));
		  endcase
	    endcase
	 end;

      // The next value for inputReg is computed.
      let newIn =
         begin
	    case (ins.wget) matches
	       // There is a new request coming from the MIF (note that the
	       // MIF interface method would not have allowed it if we
	       // couldn't handle it now):
	       tagged Valid {.x,.t}: (Valid (tuple3(0, L1 (tuple3(x[31:16], x[15:8], x[7:0])), t)));
		  
	       // No new request:
	       tagged Invalid:
		  case (newOut) matches
		     // If the output from the ring has reached its maximum
		     // cycle count, discard it and create a bubble.
		     // Otherwise send it round again.
		     tagged Valid {.c,.*,.*}:  (c == cycles ? Invalid :
					       newOut);
		     // Bubble: send on.
		     tagged Invalid:          (Invalid);
		  endcase
	    endcase
	 end;

      // Set the registers to their new values.
      outputReg <= newOut;
      inputReg <= newIn;
   endrule: doThings

   // Finally the interfaces to the MIF and the RAM
   
   interface Server mif;
      interface Put request;
	 // Accept a request if a suitable slot is coming by on the ring; put
	 // the request on the RWire ins, for processing by the rule
	 // "doThings": 
	 method put (xt) if (inReady(shift.sout));
	    action
	       ins.wset(xt);
	    endaction
	 endmethod: put
      endinterface: request
      interface Get response;
	 // Supply a response if one is available in outputReg at this moment: 
	 method get() if (outputReady(outputReg));
	    actionvalue
	       return (getOutput(outputReg));
	    endactionvalue
	 endmethod: get
      endinterface: response
   endinterface: mif
   
   interface Client ram;
      interface Get request;
	 // Make a request to the RAM if the contents of the inputReg require
	 // it:
	 method get() if (makeReq(inputReg)) ;
	    actionvalue
	       let req = 
	       case (inputReg) matches
		  tagged Valid {.*,tagged L1 {.addr,.*,.*},.*} :  return(zeroExtend(addr));
		  tagged Valid {.*,tagged L2 {.addr,.*},.*} :     return(addr);
		  tagged Valid {.*,tagged L3 .addr,.*} :          return(addr);
		  tagged Valid {.*,tagged D .*,.*} :              return(?);
	       endcase;
	       return(Read (req));
	    endactionvalue
	 endmethod: get
	 
      endinterface: request
      interface Put response;
	 // A response from the RAM is absorbed and put on the RWire rep for
	 // processing by the rule "doThings":
	 method put(d) ;
	    action
	       rep.wset(d);
	    endaction
	 endmethod: put
      endinterface: response
   endinterface: ram
endmodule: mkMesaLpm

endpackage: MesaStaticLpm
