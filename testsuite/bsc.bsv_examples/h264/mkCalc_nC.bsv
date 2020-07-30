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
// nC Calculator implementation
//----------------------------------------------------------------------
//
//

package mkCalc_nC;

import H264Types::*;
import ICalc_nC::*;
import FIFO::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;


(* synthesize *)
module mkCalc_nC( Calc_nC );

   Reg#(Bit#(PicWidthSz)) picWidth       <- mkReg(maxPicWidthInMB);
   Reg#(Bit#(PicAreaSz))  firstMb        <- mkReg(0);
   Reg#(Bit#(PicAreaSz))  currMb         <- mkReg(0);
   Reg#(Bit#(PicAreaSz))  currMbHor      <- mkReg(0);//horizontal position of currMb
   Reg#(Bit#(1))          waiting        <- mkReg(0);
   Reg#(Bit#(1))          reqCount       <- mkReg(0);
   Reg#(Bit#(2))          respCount      <- mkReg(0);
   Reg#(Bit#(1))          ipcmCount      <- mkReg(0);
   Reg#(Bit#(PicAreaSz))  pskipCount     <- mkReg(0);
   Reg#(Bit#(20))         leftVal        <- mkReg(0);
   Reg#(Bit#(20))         topVal         <- mkReg(0);
   Reg#(Bit#(10))         leftValChroma0 <- mkReg(0);
   Reg#(Bit#(10))         topValChroma0  <- mkReg(0);
   Reg#(Bit#(10))         leftValChroma1 <- mkReg(0);
   Reg#(Bit#(10))         topValChroma1  <- mkReg(0);
   FIFO#(MemReq#(TAdd#(PicWidthSz,1),20)) memReqQ  <- mkFIFO;
   FIFO#(MemResp#(20))                    memRespQ <- mkFIFO;
   Bit#(1) bit1 = 1;
   Bit#(1) bit0 = 0;
 
   rule currMbHorUpdate( !(currMbHor<zeroExtend(picWidth)) );
      Bit#(PicAreaSz) temp = zeroExtend(picWidth);
      if((currMbHor >> 3) >= temp)
	 currMbHor <= currMbHor - (temp << 3);
      else
	 currMbHor <= currMbHor - temp;
   endrule

   rule sendReq ( waiting == 1 && reqCount > 0 );
      Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
      Bit#(TAdd#(PicWidthSz,1)) temp  = {bit1,temp2};
      memReqQ.enq(tagged LoadReq temp );
      reqCount <= reqCount-1;
   endrule

   rule receiveResp ( waiting == 1 &&& respCount > 0 &&& memRespQ.first() matches tagged LoadResp .data );
      if( respCount == 2 )
	 topVal <= data;
      else
	 begin
	    topValChroma0 <= data[9:0];
	    topValChroma1 <= data[19:10];
	    waiting <= 0;
	 end
      memRespQ.deq();
      respCount <= respCount - 1;
   endrule

   rule ipcmReq ( waiting == 1 && ipcmCount > 0 );
      currMb <= currMb+1;
      currMbHor <= currMbHor+1;
      Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
      Bit#(TAdd#(PicWidthSz,1)) temp  = {bit1,temp2};
      memReqQ.enq(tagged StoreReq {addr:temp,data:20'b10000100001000010000} );
      ipcmCount <= 0;
      waiting <= 0;
   endrule

   rule pskipReq ( waiting == 1 && pskipCount > 0 && currMbHor<zeroExtend(picWidth) );
      if(pskipCount[0] == 1)
	 begin
	    currMb <= currMb+1;
	    currMbHor <= currMbHor+1;
	    Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
	    Bit#(TAdd#(PicWidthSz,1)) temp  = {bit1,temp2};
	    memReqQ.enq(StoreReq {addr:temp,data:20'b00000000000000000000} );
	    if(pskipCount == 1)
	       waiting <= 0;
	 end
      else
	 begin
	    Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
	    Bit#(TAdd#(PicWidthSz,1)) temp  = {bit0,temp2};
	    memReqQ.enq(StoreReq {addr:temp,data:20'b00000000000000000000} );
	 end
      pskipCount <= pskipCount - 1;
   endrule

   method Action initialize_picWidth( Bit#(PicWidthSz) picWidthInMb ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      picWidth  <= picWidthInMb;
   endmethod
   
   method Action initialize( Bit#(PicAreaSz) firstMbAddr ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      firstMb   <= firstMbAddr;
      currMb    <= firstMbAddr;
      currMbHor <= firstMbAddr;
      leftVal   <= 0;
      leftValChroma0 <= 0;
      leftValChroma1 <= 0;
   endmethod

   method Action loadMb( Bit#(PicAreaSz) mbAddr ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      if( mbAddr != currMb )
	 $display( "ERROR EntropyDec: mkCalc_nC loadMb wrong mbAddr" );
      else
	 begin
	    if( currMbHor == 0 || currMb == firstMb)
	       begin
		  leftVal <= 20'b11111111111111111111;
		  leftValChroma0 <= 10'b1111111111;
		  leftValChroma1 <= 10'b1111111111;
	       end
	    if( currMb-firstMb < zeroExtend(picWidth) )
	       begin
		  topVal <= 20'b11111111111111111111;
		  topValChroma0 <= 10'b1111111111;
		  topValChroma1 <= 10'b1111111111;
	       end
	    else
	       begin
		  waiting <= 1;
		  reqCount <= 1;
		  respCount <= 2;
		  Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
		  Bit#(TAdd#(PicWidthSz,1)) temp  = {bit0,temp2};
		  memReqQ.enq(tagged LoadReq temp );
		  //$display( "ERROR EntropyDec: mkCalc_nC loadMb incomplete" );
	       end
	 end
   endmethod

   method Bit#(5) nCcalc_luma( Bit#(4) microBlockNum ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      Bit#(6) templeft = 0;
      Bit#(6) temptop  = 0;
      if(microBlockNum[3]==0 && microBlockNum[1]==0)
	 templeft = zeroExtend(leftVal[4:0]);
      else if(microBlockNum[3]==0 && microBlockNum[1]==1)
	 templeft = zeroExtend(leftVal[9:5]);
      else if(microBlockNum[3]==1 && microBlockNum[1]==0)
	 templeft = zeroExtend(leftVal[14:10]);
      else
	 templeft = zeroExtend(leftVal[19:15]);
      if(microBlockNum[2]==0 && microBlockNum[0]==0)
	 temptop = zeroExtend(topVal[4:0]);
      else if(microBlockNum[2]==0 && microBlockNum[0]==1)
	 temptop = zeroExtend(topVal[9:5]);
      else if(microBlockNum[2]==1 && microBlockNum[0]==0)
	 temptop = zeroExtend(topVal[14:10]);
      else
	 temptop = zeroExtend(topVal[19:15]);
      if(temptop!=6'b011111 && templeft!=6'b011111)
	 return truncate((temptop+templeft+1) >> 1);
      else if(templeft!=6'b011111)
	 return truncate(templeft);
      else if(temptop!=6'b011111)
	 return truncate(temptop);
      else
	 return 0;
   endmethod

   method Bit#(5) nCcalc_chroma( Bit#(3) microBlockNum ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      Bit#(6) templeft = 0;
      Bit#(6) temptop  = 0;
      if(microBlockNum[2]==0)
	 begin
	    if(microBlockNum[1]==0)
	       templeft = zeroExtend(leftValChroma0[4:0]);
	    else
	       templeft = zeroExtend(leftValChroma0[9:5]);
	    if(microBlockNum[0]==0)
	       temptop = zeroExtend(topValChroma0[4:0]);
	    else
	       temptop = zeroExtend(topValChroma0[9:5]);
	 end
      else
	 begin
	    if(microBlockNum[1]==0)
	       templeft = zeroExtend(leftValChroma1[4:0]);
	    else
	       templeft = zeroExtend(leftValChroma1[9:5]);
	    if(microBlockNum[0]==0)
	       temptop = zeroExtend(topValChroma1[4:0]);
	    else
	       temptop = zeroExtend(topValChroma1[9:5]);
	 end
      if(temptop!=6'b011111 && templeft!=6'b011111)
	 return truncate((temptop+templeft+1) >> 1);
      else if(templeft!=6'b011111)
	 return truncate(templeft);
      else if(temptop!=6'b011111)
	 return truncate(temptop);
      else
	 return 0;
   endmethod

   method Action  nNupdate_luma( Bit#(4) microBlockNum, Bit#(5) totalCoeff ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      Bit#(20) topValTemp = topVal;
      if(microBlockNum[3]==0 && microBlockNum[1]==0)
	 leftVal <= {leftVal[19:5] , totalCoeff};
      else if(microBlockNum[3]==0 && microBlockNum[1]==1)
	 leftVal <= {{leftVal[19:10] , totalCoeff} , leftVal[4:0]};
      else if(microBlockNum[3]==1 && microBlockNum[1]==0)
	 leftVal <= {{leftVal[19:15] , totalCoeff} , leftVal[9:0]};
      else
	 leftVal <= {totalCoeff , leftVal[14:0]};
      if(microBlockNum[2]==0 && microBlockNum[0]==0)
	 topValTemp = {topVal[19:5] , totalCoeff};
      else if(microBlockNum[2]==0 && microBlockNum[0]==1)
	 topValTemp = {{topVal[19:10] , totalCoeff} , topVal[4:0]};
      else if(microBlockNum[2]==1 && microBlockNum[0]==0)
	 topValTemp = {{topVal[19:15] , totalCoeff} , topVal[9:0]};
      else
	 topValTemp = {totalCoeff , topVal[14:0]};
      topVal <= topValTemp;
      if(microBlockNum == 15)
	 begin
	    Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
	    Bit#(TAdd#(PicWidthSz,1)) temp  = {bit0,temp2};
	    memReqQ.enq(StoreReq {addr:temp,data:topValTemp} );
	 end
      //$display( "TRACE nNupdate_luma old leftVal %b", leftVal );
      //$display( "TRACE nNupdate_luma old topVal %b", topVal );
      //$display( "TRACE nNupdate_luma microBlockNum %0d", microBlockNum );
      //$display( "TRACE nNupdate_luma totalCoeff %0d", totalCoeff );
   endmethod
   
   method Action  nNupdate_chroma( Bit#(3) microBlockNum, Bit#(5) totalCoeff ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      Bit#(10) topValChroma0Temp = topValChroma0;
      Bit#(10) topValChroma1Temp = topValChroma1;
      if(microBlockNum[2]==0)
	 begin
	    if(microBlockNum[1]==0)
	       leftValChroma0 <= {leftValChroma0[9:5] , totalCoeff};
	    else
	       leftValChroma0 <= {totalCoeff , leftValChroma0[4:0]};
	    if(microBlockNum[0]==0)
	       topValChroma0Temp = {topValChroma0[9:5] , totalCoeff};
	    else
	       topValChroma0Temp = {totalCoeff , topValChroma0[4:0]};
	 end
      else
	 begin
	    if(microBlockNum[1]==0)
	       leftValChroma1 <= {leftValChroma1[9:5] , totalCoeff};
	    else
	       leftValChroma1 <= {totalCoeff , leftValChroma1[4:0]};
	    if(microBlockNum[0]==0)
	       topValChroma1Temp = {topValChroma1[9:5] , totalCoeff};
	    else
	       topValChroma1Temp = {totalCoeff , topValChroma1[4:0]};	    
	 end
      topValChroma0 <= topValChroma0Temp;
      topValChroma1 <= topValChroma1Temp;
      if(microBlockNum == 7)
	 begin
	    currMb <= currMb+1;
	    currMbHor <= currMbHor+1;
	    Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
	    Bit#(TAdd#(PicWidthSz,1)) temp  = {bit1,temp2};
	    memReqQ.enq(StoreReq {addr:temp,data:{topValChroma1Temp,topValChroma0Temp}} );
	 end
   endmethod

   method Action  nNupdate_pskip( Bit#(PicAreaSz) inmb_skip_run ) if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      //$display( "TRACE nNupdate_pskip mb_skip_run = %0d", inmb_skip_run );

      if(inmb_skip_run > 0)
	 begin
	    waiting <= 1;
	    pskipCount <= (inmb_skip_run << 1)-1;
	    Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
	    Bit#(TAdd#(PicWidthSz,1)) temp  = {bit0,temp2};
	    memReqQ.enq(StoreReq {addr:temp,data:20'b00000000000000000000} );
	    leftVal <= 0;
	    leftValChroma0 <= 10'b0000000000;
	    leftValChroma1 <= 10'b0000000000;
	 end
   endmethod
   
   method Action  nNupdate_ipcm() if( waiting == 0 && currMbHor<zeroExtend(picWidth) );
      leftVal <= 20'b10000100001000010000;
      leftValChroma0 <= 10'b1000010000;
      leftValChroma1 <= 10'b1000010000;
      //$display( "TRACE nNupdate_ipcm");

      waiting <= 1;
      ipcmCount <= 1;
      Bit#(PicWidthSz)          temp2 = truncate(currMbHor);
      Bit#(TAdd#(PicWidthSz,1)) temp  = {bit0,temp2};
      memReqQ.enq(StoreReq {addr:temp,data:20'b10000100001000010000} );
   endmethod

   interface Client mem_client;
      interface Get request  = fifoToGet(memReqQ);
      interface Put response = fifoToPut(memRespQ);
   endinterface


endmodule



endpackage
