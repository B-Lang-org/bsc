package ClientServerLib;

// This package supplies two little functions which might well be included in
// the standard ClientServer library.

import FIFO::*;
import GetPut::*;
import ClientServer::*;

function Client#(a,b)
   mkClientFromFIFOs (FIFO#(a) req_fifo, FIFO#(b) res_fifo);
   return (interface Client;
	      interface Get request = fifoToGet(req_fifo);
	      interface Put response = fifoToPut(res_fifo);
	   endinterface: Client);
endfunction

function Server#(a,b)
   mkServerFromFIFOs (FIFO#(a) req_fifo, FIFO#(b) res_fifo);
   return (interface Server;
	      interface Put request = fifoToPut(req_fifo);
              interface Get response = fifoToGet(res_fifo);
	   endinterface: Server);
endfunction

endpackage: ClientServerLib
