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
// Interface for nC Calculator
//----------------------------------------------------------------------
//
//
//

package ICalc_nC;

import H264Types::*;
import GetPut::*;
import ClientServer::*;

interface Calc_nC;
   method Action  initialize_picWidth( Bit#(PicWidthSz) picWidthInMb );
   method Action  initialize( Bit#(PicAreaSz) firstMbAddr );
   method Action  loadMb( Bit#(PicAreaSz) mbAddr );
   method Bit#(5) nCcalc_luma( Bit#(4) microBlockNum );
   method Bit#(5) nCcalc_chroma( Bit#(3) microBlockNum );
   method Action  nNupdate_luma( Bit#(4) microBlockNum, Bit#(5) updataVal );
   method Action  nNupdate_chroma( Bit#(3) microBlockNum, Bit#(5) updataVal );
   method Action  nNupdate_pskip( Bit#(PicAreaSz) mb_skip_run );
   method Action  nNupdate_ipcm();
   interface Client#(MemReq#(TAdd#(PicWidthSz,1),20),MemResp#(20)) mem_client;
endinterface

endpackage

