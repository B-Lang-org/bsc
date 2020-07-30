////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package ClientServerLib;

export mkClientFromFIFOs;
export mkServerFromFIFOs;

import FIFO::*;
import GetPut::*;
import ClientServer::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Client#(a,b)
   mkClientFromFIFOs (FIFO#(a) req_fifo, FIFO#(b) res_fifo);
   return (interface Client;
	      method request();
	         return (interface Get;
			    method get();
			       actionvalue
			          req_fifo.deq();
			          return req_fifo.first();
			       endactionvalue
			    endmethod: get
			 endinterface: Get);
	      endmethod: request

	      method response();
	         return (interface Put;
			    method put(b val);
			       return res_fifo.enq(val);
			    endmethod: put
			 endinterface: Put);
	      endmethod: response
	   endinterface: Client);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Server#(a,b)
   mkServerFromFIFOs (FIFO#(a) req_fifo, FIFO#(b) res_fifo);
   return (interface Server;
	      method request();
	         return (interface Put;
			    method put(b val);
			       return req_fifo.enq(val);
			    endmethod: put
			 endinterface: Put);
	      endmethod: request

	      method response();
	         return (interface Get;
			    method get();
			       actionvalue
			          res_fifo.deq();
			          return res_fifo.first();
			       endactionvalue
			    endmethod: get
			 endinterface: Get);
	      endmethod: response
	   endinterface: Server);
endfunction

endpackage: ClientServerLib

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

