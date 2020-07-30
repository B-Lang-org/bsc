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
// Interface for H264 Main Module
//----------------------------------------------------------------------
//
//
//

package IH264;

import H264Types::*;
import GetPut::*;
import ClientServer::*;

interface IH264;

   // Interface for memory, input generator
   interface Put#(InputGenOT)                    ioin;
   interface Client#(MemReq#(TAdd#(PicWidthSz,1),20),MemResp#(20)) mem_clientED;
   interface Client#(MemReq#(TAdd#(PicWidthSz,2),68),MemResp#(68)) mem_clientP_intra;
   interface Client#(MemReq#(TAdd#(PicWidthSz,2),32),MemResp#(32)) mem_clientP_inter;
   interface Client#(MemReq#(PicWidthSz,13),MemResp#(13)) mem_clientD_parameter;
   interface Client#(MemReq#(TAdd#(PicWidthSz,5),32),MemResp#(32)) mem_clientD_data;
   interface Client#(FrameBufferLoadReq,FrameBufferLoadResp) buffer_client_load1;
   interface Client#(FrameBufferLoadReq,FrameBufferLoadResp) buffer_client_load2;
   interface Get#(FrameBufferStoreReq) buffer_client_store;
   interface Get#(BufferControlOT) ioout;

endinterface

endpackage

