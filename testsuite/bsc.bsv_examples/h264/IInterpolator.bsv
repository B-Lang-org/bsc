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
// Interface for interpolator
//----------------------------------------------------------------------
//
//
//

package IInterpolator;

import H264Types::*;
import GetPut::*;
import Vector::*;
import ClientServer::*;

interface Interpolator;
   method Action   setPicWidth( Bit#(PicWidthSz) newPicWidth );
   method Action   setPicHeight( Bit#(PicHeightSz) newPicHeight );
   method Action   request( InterpolatorIT inputdata );
   method Vector#(4,Bit#(8)) first();
   method Action   deq();
   method Action   endOfFrame();
   interface Client#(InterpolatorLoadReq,InterpolatorLoadResp) mem_client;
endinterface

endpackage

