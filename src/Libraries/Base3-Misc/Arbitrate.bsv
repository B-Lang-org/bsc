////////////////////////////////////////////////////////////////////////////////
//  Filename      : Arbitrate.bsv
//  Description   :
////////////////////////////////////////////////////////////////////////////////
package Arbitrate;

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Vector            ::*;
import GetPut            ::*;
import ClientServer      ::*;
import FIFOF             ::*;
import FIFO              ::*;

////////////////////////////////////////////////////////////////////////////////
/// Exports
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typeclass ArbRequestTC#(type a);
   function Bool isReadRequest(a x);
   function Bool isWriteRequest(a x);
endtypeclass

////////////////////////////////////////////////////////////////////////////////
/// Functions
////////////////////////////////////////////////////////////////////////////////
function Vector#(n, Bool) select_grant(Vector#(n, Bool) requests, UInt#(TLog#(n)) lowpriority);
   let nports = valueOf(n);

   function f(bspg,b);
      match {.bs, .p, .going} = bspg;
      if (going) begin
	 if (b) return tuple3(1 << p, ?, False);
	 else   return tuple3(0, (p == fromInteger(nports-1) ? 0 : p+1), True);
      end
      else return tuple3(bs, ?, False);
   endfunction

   match {.bits, .*, .* } = foldl(f, tuple3(?, lowpriority, True), reverse(rotateBy(reverse(requests), lowpriority)));
   return unpack(bits);
endfunction

function Bool hasRequest(FIFOF#(a) b);
   return b.notEmpty;
endfunction

function Server#(req,resp) fifosToServer(Tuple2#(FIFOF#(req), FIFO#(resp)) a);
   return (interface Server
	      interface request  = toPut(tpl_1(a));
	      interface response = toGet(tpl_2(a));
	   endinterface);
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////
interface Arbitrate#(numeric type size);
   method    Action              request(Vector#(size, Bool) req);
   method    Vector#(size, Bool) grant;
endinterface

interface Arbiter#(numeric type ports, type request, type response);
   interface Vector#(ports, Server#(request, response)) users;
   interface Client#(request, response)                 master;
endinterface

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of Pseudo Round Robin Arbitration
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
(* options = {"-aggressive-conditions, -no-opt-AndOr"} *)
module mkRoundRobin(Arbitrate#(n))
   provisos(  Add#(1, z, n)
	    , Log#(n, logn)
	    );

   Integer maxCounter = valueOf(n) - 1;

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(UInt#(logn))          rLowPriority        <- mkReg(0);
   Vector#(n, Wire#(Bool))    vwCurrGrant         <- replicateM(mkDWire(False));

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method Action request(Vector#(n, Bool) requests);
      rLowPriority <= rLowPriority + 1;
      if (pack(requests) == 0) writeVReg(vwCurrGrant, replicate(False));
      else                     writeVReg(vwCurrGrant, select_grant(requests, rLowPriority));
   endmethod

   method Vector#(n, Bool) grant;
      return map(readReg, vwCurrGrant);
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation of Fixed Priority Arbitration
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
(* options = {"-aggressive-conditions, -no-opt-AndOr"} *)
module mkFixedPriority(Arbitrate#(n))
   provisos(  Add#(1, z, n)
	    , Log#(n, logn)
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Vector#(n, Wire#(Bool))    vwCurrGrant         <- replicateM(mkDWire(False));

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   method Action request(Vector#(n, Bool) requests);
      if (pack(requests) == 0) writeVReg(vwCurrGrant, replicate(False));
      else                     writeVReg(vwCurrGrant, select_grant(requests, 0));
   endmethod

   method Vector#(n, Bool) grant;
      return map(readReg, vwCurrGrant);
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Implementation
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
module mkArbiter#(Arbitrate#(n) arbIfc, Integer max_in_flight)(Arbiter#(n, req, resp))
   provisos(  Add#(1, _1, n)     // must have at least one user
	    , Bits#(req, sreq)   // requests must be bit representable
	    , Bits#(resp, sresp) // responses must be bit representable
	    , ArbRequestTC#(req) // supports a request with a read/write distinction
	    );

   ////////////////////////////////////////////////////////////////////////////////
   /// Design Elements
   ////////////////////////////////////////////////////////////////////////////////
   Vector#(n, FIFOF#(req))         vfRequests          <- replicateM(mkFIFOF);
   Vector#(n, FIFO#(resp))         vfResponses         <- replicateM(mkFIFO);

   FIFO#(UInt#(TLog#(n)))          fMasterReadIds      <- mkSizedFIFO(max_in_flight);
   FIFO#(req)                      fMasterReq          <- mkFIFO;
   FIFO#(resp)                     fMasterResp         <- mkFIFO;

   ////////////////////////////////////////////////////////////////////////////////
   /// Rules
   ////////////////////////////////////////////////////////////////////////////////
   (* fire_when_enabled, no_implicit_conditions *)
   rule arbitrate if (any(hasRequest, vfRequests));
      arbIfc.request(map(hasRequest, vfRequests));
   endrule

   (* aggressive_implicit_conditions *)
   rule route_read_requests if (findElem(True, arbIfc.grant) matches tagged Valid .grantid
				&&& isReadRequest(vfRequests[grantid].first)
			       );
      let request <- toGet(vfRequests[grantid]).get;
      fMasterReq.enq(request);
      fMasterReadIds.enq(grantid);
   endrule

   (* aggressive_implicit_conditions *)
   rule route_write_requests if (findElem(True, arbIfc.grant) matches tagged Valid .grantid
				 &&& isWriteRequest(vfRequests[grantid].first)
				);
      let request <- toGet(vfRequests[grantid]).get;
      fMasterReq.enq(request);
   endrule

   rule route_responses;
      let response <- toGet(fMasterResp).get;
      let respid <- toGet(fMasterReadIds).get;
      vfResponses[respid].enq(response);
   endrule

   ////////////////////////////////////////////////////////////////////////////////
   /// Interface Connections / Methods
   ////////////////////////////////////////////////////////////////////////////////
   interface users = map(fifosToServer, zip(vfRequests, vfResponses));

   interface Client master;
      interface request  = toGet(fMasterReq);
      interface response = toPut(fMasterResp);
   endinterface

endmodule

endpackage: Arbitrate

