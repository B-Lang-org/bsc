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
// H264 Test Bench
//----------------------------------------------------------------------
//
//

package mkTH;

import H264Types::*;
import IMemED::*;
import IFrameBuffer::*;
import IInputGen::*;
import IFinalOutput::*;
import IH264::*;
import mkMemED::*;
import mkFrameBuffer::*;
import mkInputGen::*;
import mkFinalOutput::*;
import mkH264::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;

(* synthesize *)
module mkTH( Empty );

   // Instantiate the modules

   IInputGen     inputgen    <- mkInputGen();
   IH264         h264        <- mkH264();
   IMemED#(TAdd#(PicWidthSz,1),20) memED          <- mkMemED();
   IMemED#(TAdd#(PicWidthSz,2),68) memP_intra     <- mkMemED();
   IMemED#(TAdd#(PicWidthSz,2),32) memP_inter     <- mkMemED();
   IMemED#(TAdd#(PicWidthSz,5),32) memD_data      <- mkMemED();
   IMemED#(PicWidthSz,13)          memD_parameter <- mkMemED();
   IFrameBuffer   framebuffer   <- mkFrameBuffer();
   IFinalOutput   finaloutput   <- mkFinalOutput();

   // Cycle counter
   Reg#(Bit#(32)) cyclecount <- mkReg(0);

   rule countCycles ( True );
      if(cyclecount[4:0]==0) $display( "CCLCycleCount %0d", cyclecount );
      cyclecount <= cyclecount+1;
      if(cyclecount > 600000000)
	 begin
	    $display( "ERROR mkTH: time out" );
	    $finish(0);
	 end
   endrule
   
   // Internal connections
   
   mkConnection( inputgen.ioout, h264.ioin );
   mkConnection( h264.mem_clientED, memED.mem_server );
   mkConnection( h264.mem_clientP_intra, memP_intra.mem_server );
   mkConnection( h264.mem_clientP_inter, memP_inter.mem_server );
   mkConnection( h264.mem_clientD_data, memD_data.mem_server );
   mkConnection( h264.mem_clientD_parameter, memD_parameter.mem_server );
   mkConnection( h264.buffer_client_load1, framebuffer.server_load1 );
   mkConnection( h264.buffer_client_load2, framebuffer.server_load2 );
   mkConnection( h264.buffer_client_store, framebuffer.server_store );
   mkConnection( h264.ioout, finaloutput.ioin );
   
endmodule

endpackage
