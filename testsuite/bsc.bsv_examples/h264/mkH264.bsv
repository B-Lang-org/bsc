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
// H264 Main Module
//----------------------------------------------------------------------
//
//

package mkH264;

import H264Types::*;
import IH264::*;
import INalUnwrap::*;
import IEntropyDec::*;
import IInverseTrans::*;
import IPrediction::*;
import IDeblockFilter::*;
import IBufferControl::*;
import mkNalUnwrap::*;
import mkEntropyDec::*;
import mkInverseTrans::*;
import mkPrediction::*;
import mkDeblockFilter::*;
import mkBufferControl::*;
import EntropyTee::*;
import DeblockTee::*;
 
import Connectable::*;
import GetPut::*;
import ClientServer::*;

(* synthesize *)
module mkH264( IH264 );

   // Instantiate the modules

   INalUnwrap     nalunwrap     <- mkNalUnwrap();
   IEntropyDec    entropydec    <- mkEntropyDec();
   IInverseTrans  inversetrans  <- mkInverseTrans();
   IPrediction    prediction    <- mkPrediction();
   IDeblockFilter deblockfilter <- mkDeblockFilter();
   IBufferControl buffercontrol <- mkBufferControl();

   // Internal connections
   mkConnection( prediction.mem_client_buffer, buffercontrol.inter_server );

   mkConnection( nalunwrap.ioout, entropydec.ioin );
   mkConnection( entropydec.ioout_InverseTrans, inversetrans.ioin );
   mkConnection( entropydec.ioout, prediction.ioin );
   mkConnection( inversetrans.ioout, prediction.ioin_InverseTrans );
   mkConnection(prediction.ioout, deblockfilter.ioin);
   mkConnection( deblockfilter.ioout, buffercontrol.ioin);

   // Interface to input generator
   interface ioin = nalunwrap.ioin;
   
   // Memory interfaces
   interface mem_clientED          = entropydec.mem_client; 
   interface mem_clientP_intra     = prediction.mem_client_intra;
   interface mem_clientP_inter     = prediction.mem_client_inter;
   interface mem_clientD_data      = deblockfilter.mem_client_data;
   interface mem_clientD_parameter = deblockfilter.mem_client_parameter;
   interface buffer_client_load1   = buffercontrol.buffer_client_load1;
   interface buffer_client_load2   = buffercontrol.buffer_client_load2;
   interface buffer_client_store   = buffercontrol.buffer_client_store;

   // Interface for output 
   interface ioout = buffercontrol.ioout;
      
endmodule

endpackage
