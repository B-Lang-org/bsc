package Arbiter;

import Vector::*;
import BUtils::*;
import Connectable::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ArbiterClient_IFC;
   method Action request();
   method Action lock();
   method Bool grant();
endinterface

interface ArbiterRequest_IFC;
   method Bool request();
   method Bool lock();
   method Action grant();
endinterface

interface Arbiter_IFC#(numeric type count);
   interface Vector#(count, ArbiterClient_IFC) clients;
   method    Bit#(TLog#(count))                grant_id;
endinterface

////////////////////////////////////////////////////////////////////////////////
/// A fair round robin arbiter with changing priorities. If the value of "fixed"
/// is True, the current grant is locked and not updated again until
/// "fixed" goes False;
////////////////////////////////////////////////////////////////////////////////

module mkArbiter#(Bool fixed) (Arbiter_IFC#(count));

   let icount = valueOf(count);

   // Initially, priority is given to client 0
   Vector#(count, Bool) init_value = replicate(False);
   init_value[0] = True;
   Reg#(Vector#(count, Bool)) priority_vector <- mkReg(init_value);


   Wire#(Vector#(count, Bool)) grant_vector   <- mkBypassWire;
   Wire#(Bit#(TLog#(count)))   grant_id_wire  <- mkBypassWire;
   Vector#(count, PulseWire) request_vector <- replicateM(mkPulseWire);

   rule every (True);

      // calculate the grant_vector
      Vector#(count, Bool) zow = replicate(False);
      Vector#(count, Bool) grant_vector_local = replicate(False);
      Bit#(TLog#(count))   grant_id_local     = 0;

      Bool found = True;

      for (Integer x = 0; x < (2 * icount); x = x + 1)

	 begin

	    Integer y = (x % icount);

	    if (priority_vector[y]) found = False;

	    let a_request = request_vector[y];
	    zow[y] = a_request;

	    if (!found && a_request)
	       begin
		  grant_vector_local[y] = True;
		  grant_id_local        = fromInteger(y);
		  found = True;
	       end
	 end

      // Update the RWire
      grant_vector  <= grant_vector_local;
      grant_id_wire <= grant_id_local;

      // If a grant was given, update the priority vector so that
      // client now has lowest priority.
      if (any(isTrue,grant_vector_local) && !fixed)
	 begin
//	    $display("(%5d) Updating priorities", $time);
	    priority_vector <= rotateR(grant_vector_local);
	 end


//      $display("(%5d)  priority vector: %4b", $time, priority_vector);
//      $display("(%5d)   request vector: %4b", $time, zow);
//      $display("(%5d)     Grant vector: %4b", $time, grant_vector_local);

   endrule

   // Now create the vector of interfaces
   Vector#(count, ArbiterClient_IFC) client_vector = newVector;

   for (Integer x = 0; x < icount; x = x + 1)

      client_vector[x] = (interface ArbiterClient_IFC

			     method Action request();
				request_vector[x].send();
			     endmethod

			     method Action lock();
				dummyAction;
			     endmethod

			     method grant ();
				return grant_vector[x];
			     endmethod
			  endinterface);

   interface clients = client_vector;
   method    grant_id = grant_id_wire;
endmodule

////////////////////////////////////////////////////////////////////////////////
/// This one gives the current owner priority (i.e. they can hold as long as
/// they keep requesting it.
////////////////////////////////////////////////////////////////////////////////

module mkStickyArbiter (Arbiter_IFC#(count));

   let icount = valueOf(count);

   // Initially, priority is given to client 0
   Vector#(count, Bool) all_false = replicate(False);
   Vector#(count, Bool) init_value = replicate(False);
   init_value[0] = True;
   Reg#(Vector#(count, Bool)) priority_vector <- mkReg(init_value);


   Wire#(Vector#(count, Bool)) grant_vector      <- mkBypassWire;
   Reg#(Vector#(count, Bool))  grant_vector_prev <- mkReg(all_false);
   Wire#(Bit#(TLog#(count)))   grant_id_wire     <- mkBypassWire;
   Vector#(count, PulseWire) request_vector <- replicateM(mkPulseWire);

   function Bool getValue(PulseWire ifc);
      return ifc._read;
   endfunction

   rule every (True);

      let current_requests = map(getValue, request_vector);
      let owner_request = (pack(grant_vector_prev) & pack(current_requests)) != 0;

      // calculate the grant_vector
      Vector#(count, Bool) zow = all_false;
      Vector#(count, Bool) grant_vector_local = all_false;
      Bit#(TLog#(count))   grant_id_local     = 0;

      if (owner_request)
	 grant_vector_local = grant_vector_prev;
      else
	 begin

	    Bool found = True;

	    for (Integer x = 0; x < (2 * icount); x = x + 1)

	       begin

		  Integer y = (x % icount);

		  if (priority_vector[y]) found = False;

		  let a_request = request_vector[y];
		  zow[y] = a_request;

		  if (!found && a_request)
		     begin
			grant_vector_local[y] = True;
			grant_id_local        = fromInteger(y);
			found = True;
		     end
	       end
	 end


      // Update the RWire
      grant_vector      <= grant_vector_local;
      grant_vector_prev <= grant_vector_local;
      grant_id_wire     <= grant_id_local;

      // If a new grant was given, update the priority vector so that
      // client now has lowest priority.
      if (any(isTrue, grant_vector_local) && !owner_request)

	 priority_vector <= rotateR(grant_vector_local);
/* -----\/----- EXCLUDED -----\/-----

      $display("  priority vector %4b", priority_vector, $time);
      $display("   request vector %4b", zow, $time);
      $display("     Grant vector %4b", grant_vector_local, $time);
      $display("Grant vector prev %4b", grant_vector_prev, $time);
 -----/\----- EXCLUDED -----/\----- */

   endrule

   // Now create the vector of interfaces
   Vector#(count, ArbiterClient_IFC) client_vector = newVector;

   for (Integer x = 0; x < icount; x = x + 1)

      client_vector[x] = (interface ArbiterClient_IFC

			     method Action request();
				request_vector[x].send();
			     endmethod

			     method Action lock();

			     endmethod

			     method grant ();
				return grant_vector_prev[x];
			     endmethod
			  endinterface);

   interface clients = client_vector;
   method    grant_id = grant_id_wire;
endmodule

module mkHoldArbiter (Arbiter_IFC#(count));

   let icount = valueOf(count);

   // Initially, priority is given to client 0
   Vector#(count, Bool) init_value = replicate(False);
   init_value[0] = True;
   Reg#(Vector#(count, Bool)) priority_vector <- mkReg(init_value);



   Wire#(Vector#(count, Bool)) grant_vector   <- mkBypassWire;
   Wire#(Bit#(TLog#(count)))   grant_id_wire  <- mkBypassWire;
   Vector#(count, PulseWire)   request_vector <- replicateM(mkPulseWire);

   rule every (True);

      // calculate the grant_vector
      Vector#(count, Bool) zow = replicate(False);
      Vector#(count, Bool) grant_vector_local = replicate(False);
      Bit#(TLog#(count))   grant_id_local     = 0;

      Bool found = True;

      for (Integer x = 0; x < (2 * icount); x = x + 1)

	 begin

	    Integer y = (x % icount);

	    if (priority_vector[y]) found = False;

	    let a_request = request_vector[y];
	    zow[y] = a_request;

	    if (!found && a_request)
	       begin
		  grant_vector_local[y] = True;
		  grant_id_local        = fromInteger(y);
		  found = True;
	       end
	 end

      // Update the RWire
      grant_vector  <= grant_vector_local;
      grant_id_wire <= grant_id_local;

      // If a grant was given, update the priority vector so that
      // client now has lowest priority.
      if (any(isTrue,grant_vector_local))
	 begin
	    priority_vector <= rotateR(grant_vector_local);
	    grant_vector <= grant_vector_local;
	 end
      else
	 begin
	    grant_vector <= grant_vector; // hold previous values
	 end

//      $display(" priority vector %4b", priority_vector, $time);
//      $display("  request vector %4b", zow, $time);
//      $display("    Grant vector %4b", grant_vector_local, $time);

   endrule

   // Now create the vector of interfaces
   Vector#(count, ArbiterClient_IFC) client_vector = newVector;

   for (Integer x = 0; x < icount; x = x + 1)

      client_vector[x] = (interface ArbiterClient_IFC

			     method Action request();
				request_vector[x].send();
			     endmethod

			     method Action lock();
				dummyAction;
			     endmethod

			     method grant ();
				return grant_vector[x];
			     endmethod
			  endinterface);

   interface clients = client_vector;
   method    grant_id = grant_id_wire;
endmodule

function Bool isTrue(Bool value);
   return value;
endfunction

instance Connectable#(ArbiterClient_IFC,  ArbiterRequest_IFC);
   module mkConnection#(ArbiterClient_IFC client, ArbiterRequest_IFC request) (Empty);

      rule send_grant (client.grant);
	 request.grant();
      endrule

      rule send_request (request.request);
	 client.request();
      endrule

      rule send_lock (request.lock);
	 client.lock();
      endrule
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typeclass Arbitable#(type a);
   module mkArbiterRequest#(a ifc) (ArbiterRequest_IFC);
endtypeclass

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage
