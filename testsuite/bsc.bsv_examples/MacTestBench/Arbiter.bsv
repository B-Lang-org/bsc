package Arbiter;

import Vector::*;
import Connectable::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ArbiterClient_IFC;
   method Action request();
   method Bool grant();
endinterface

interface ArbiterRequest_IFC;
   method Bool request();
   method Action grant();
endinterface

interface Arbiter_IFC#(type count);
   interface Vector#(count, ArbiterClient_IFC) clients;
endinterface

////////////////////////////////////////////////////////////////////////////////
/// A fair arbiter with changing priorities.
////////////////////////////////////////////////////////////////////////////////
   
module mkArbiter (Arbiter_IFC#(count))
   provisos (Log#(count, size));

   let icount = valueOf(count);
   
   // Initially, priority is given to client 0
   Vector#(count, Bool) init_value = replicate(False);
   init_value[0] = True;
   Reg#(Vector#(count, Bool)) priority_vector <- mkReg(init_value);

  
   Wire#(Vector#(count, Bool)) grant_vector <- mkWire;
   Vector#(count, PulseWire) request_vector <- replicateM(mkPulseWire);

   rule every (True);

      // calculate the grant_vector
      Vector#(count, Bool) zow = replicate(False);
      Vector#(count, Bool) grant_vector_local = replicate(False);

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
		  found = True;
	       end
	 end

      // Update the RWire
      grant_vector <= grant_vector_local;

      // If a grant was given, update the priority vector so that
      // client now has lowest priority.
      if (any(isTrue,grant_vector_local))

	 priority_vector <= rotateR(grant_vector_local);

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

			     method grant ();
				return grant_vector[x];
			     endmethod
			  endinterface);
			   
   interface clients = client_vector;
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
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage