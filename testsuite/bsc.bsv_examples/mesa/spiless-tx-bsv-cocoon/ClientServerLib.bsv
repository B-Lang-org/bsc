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
	      interface Get request;
		 method get();
		    actionvalue
		       req_fifo.deq();
		       return req_fifo.first();
		    endactionvalue
		 endmethod: get
	      endinterface: request
	      interface Put response;
		 method put = res_fifo.enq;
	      endinterface: response
	   endinterface: Client);
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Server#(a,b)
   mkServerFromFIFOs (FIFO#(a) req_fifo, FIFO#(b) res_fifo);
   return (interface Server;
	      interface Put request;
		 method put = req_fifo.enq;
	      endinterface: request
	      interface Get response;
		 method get();
		    actionvalue
		       res_fifo.deq();
		       return res_fifo.first();
		    endactionvalue
		 endmethod: get
	      endinterface: response
	   endinterface: Server);
endfunction

endpackage: ClientServerLib

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

