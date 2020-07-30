// The MIT License

// Copyright (c) 2006-2007 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
//**********************************************************************
// Memory for Entropy Decoder
//----------------------------------------------------------------------
//
//
//

package mkMemED;

import H264Types::*;
import IMemED::*;
import RegFile::*;
import GetPut::*;
import ClientServer::*;
import FIFO::*;


//----------------------------------------------------------------------
// Main module
//----------------------------------------------------------------------

module mkMemED(IMemED#(index_size,data_size))
   provisos (Bits#(MemReq#(index_size,data_size),mReqLen),
	     Bits#(MemResp#(data_size),mRespLen));

  //-----------------------------------------------------------
  // State

   RegFile#(Bit#(index_size),Bit#(data_size)) rfile <- mkRegFileFull();
   
   FIFO#(MemReq#(index_size,data_size)) reqQ  <- mkFIFO();
   FIFO#(MemResp#(data_size))  respQ <- mkFIFO();
   
   rule storing ( reqQ.first() matches tagged StoreReq { addr:.addrt,data:.datat} );
      rfile.upd(addrt,datat);
      reqQ.deq(); 
   endrule

   rule reading ( reqQ.first() matches tagged LoadReq .addrt );
      Bit#(data_size) data = rfile.sub(addrt);
      respQ.enq( tagged LoadResp data);
      reqQ.deq();
   endrule
   
   interface Server mem_server;
      interface Put request  = fifoToPut(reqQ);
      interface Get response = fifoToGet(respQ);
   endinterface


endmodule

endpackage
