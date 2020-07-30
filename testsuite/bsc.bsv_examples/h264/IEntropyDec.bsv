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
// Interface for Entropy Decoder
//----------------------------------------------------------------------
//
//
//

package IEntropyDec;

import H264Types::*;
import GetPut::*;
import ClientServer::*;

interface IEntropyDec;

  // Interface for inter-module io
  interface Put#(NalUnwrapOT) ioin;
  interface Get#(EntropyDecOT) ioout;
  interface Get#(EntropyDecOT_InverseTrans) ioout_InverseTrans;

  // Interface for module to memory
  interface Client#(MemReq#(TAdd#(PicWidthSz,1),20),MemResp#(20)) mem_client;

endinterface

endpackage

