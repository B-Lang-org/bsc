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
// interpolator implementation
//----------------------------------------------------------------------
//
//

package mkInterpolator;

import H264Types::*;
import IInterpolator::*;
import FIFO::*;
import Vector::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;


//-----------------------------------------------------------
// Local Datatypes
//-----------------------------------------------------------

typedef union tagged
{
 struct { Bit#(2) xFracL; Bit#(2) yFracL; Bit#(2) offset; IPBlockType bt; } IPWLuma;
 struct { Bit#(3) xFracC; Bit#(3) yFracC; Bit#(2) offset; IPBlockType bt; } IPWChroma;
}
InterpolatorWT deriving(Eq,Bits);


//-----------------------------------------------------------
// Helper functions

function Bit#(8) clip1y10to8( Bit#(10) innum );
   if(innum[9] == 1)
      return 0;
   else if(innum[8] == 1)
      return 255;
   else
      return truncate(innum);
endfunction

function Bit#(15) interpolate8to15( Bit#(8) in0, Bit#(8) in1, Bit#(8) in2, Bit#(8) in3, Bit#(8) in4, Bit#(8) in5 );
   return zeroExtend(in0) - 5*zeroExtend(in1) + 20*zeroExtend(in2) + 20*zeroExtend(in3) - 5*zeroExtend(in4) + zeroExtend(in5);
endfunction

function Bit#(8) interpolate15to8( Bit#(15) in0, Bit#(15) in1, Bit#(15) in2, Bit#(15) in3, Bit#(15) in4, Bit#(15) in5 );
   Bit#(20) temp = signExtend(in0) - 5*signExtend(in1) + 20*signExtend(in2) + 20*signExtend(in3) - 5*signExtend(in4) + signExtend(in5) + 512;
   return clip1y10to8(truncate(temp>>10));
endfunction



//-----------------------------------------------------------
// Interpolation Module
//-----------------------------------------------------------


(* synthesize *)
module mkInterpolator( Interpolator );
   
   FIFO#(InterpolatorIT) reqfifoLoad <- mkSizedFIFO(interpolator_reqfifoLoad_size);
   FIFO#(InterpolatorWT) reqfifoWork1 <- mkSizedFIFO(interpolator_reqfifoWork_size);
   Reg#(Maybe#(InterpolatorWT)) reqregWork2 <- mkReg(Invalid);
   FIFO#(Vector#(4,Bit#(8))) outfifo <- mkFIFO;
   Reg#(Bool) endOfFrameFlag <- mkReg(False);
   FIFO#(InterpolatorLoadReq)  memReqQ  <- mkFIFO;
   FIFO#(InterpolatorLoadResp) memRespQ <- mkSizedFIFO(interpolator_memRespQ_size);

   Reg#(Bit#(PicWidthSz))  picWidth  <- mkReg(maxPicWidthInMB);
   Reg#(Bit#(PicHeightSz)) picHeight <- mkReg(0);

   RFile1#(Bit#(6),Vector#(4,Bit#(15))) workFile  <- mkRFile1Full();
   RFile1#(Bit#(6),Vector#(4,Bit#(8)))  storeFile <- mkRFile1Full();
   Reg#(Bit#(1)) workFileFlag <- mkReg(0);
   RFile1#(Bit#(4),Vector#(4,Bit#(8))) resultFile <- mkRFile1Full();

   Reg#(Bit#(1)) loadStage  <- mkReg(0);
   Reg#(Bit#(2)) loadHorNum <- mkReg(0);
   Reg#(Bit#(4)) loadVerNum <- mkReg(0);

   Reg#(Bit#(2)) work1MbPart    <- mkReg(0);//only for Chroma
   Reg#(Bit#(2)) work1SubMbPart <- mkReg(0);//only for Chroma
   Reg#(Bit#(1)) work1Stage     <- mkReg(0);
   Reg#(Bit#(2)) work1HorNum    <- mkReg(0);
   Reg#(Bit#(4)) work1VerNum    <- mkReg(0);
   Reg#(Vector#(20,Bit#(8))) work1Vector8 <- mkRegU;
   Reg#(Bool) work1Done <- mkReg(False);

   Reg#(Bit#(2)) work2SubMbPart <- mkReg(0);
   Reg#(Bit#(2)) work2HorNum    <- mkReg(0);
   Reg#(Bit#(4)) work2VerNum    <- mkReg(0);
   Reg#(Vector#(20,Bit#(8))) work2Vector8 <- mkRegU;
   Reg#(Vector#(20,Bit#(15))) work2Vector15 <- mkRegU;
   Reg#(Vector#(16,Bit#(1))) resultReady <- mkReg(replicate(0));
   Reg#(Bool) work2Done <- mkReg(False);
   Reg#(Bool) work8x8Done <- mkReg(False);

   Reg#(Bit#(2)) outBlockNum <- mkReg(0);
   Reg#(Bit#(2)) outPixelNum <- mkReg(0);
   Reg#(Bool) outDone <- mkReg(False);
   

   rule sendEndOfFrameReq( endOfFrameFlag );
      endOfFrameFlag <= False;
      memReqQ.enq(IPLoadEndFrame);
   endrule
   
   
   rule loadLuma( reqfifoLoad.first() matches tagged IPLuma .reqdata &&& !endOfFrameFlag );
      Bit#(2) xfracl = reqdata.mvhor[1:0];
      Bit#(2) yfracl = reqdata.mvver[1:0];
      Bit#(2) offset = reqdata.mvhor[3:2];
      Bool twoStage = (xfracl==1||xfracl==3) && (yfracl==1||yfracl==3);
      Bool horInter = (twoStage ? loadStage==1 : xfracl!=0);
      Bool verInter = (twoStage ? loadStage==0 : yfracl!=0);
      Bit#(2) offset2 = reqdata.mvhor[3:2] + ((twoStage&&verInter&&xfracl==3) ? 1 : 0);
      Bit#(1) horOut = 0;
      Bit#(TAdd#(PicWidthSz,2)) horAddr;
      Bit#(TAdd#(PicHeightSz,4)) verAddr;
      Bit#(TAdd#(PicWidthSz,12)) horTemp = zeroExtend({reqdata.hor,2'b00}) + zeroExtend({loadHorNum,2'b00}) + (xfracl==3&&(yfracl==1||yfracl==3)&&loadStage==0 ? 1 : 0);
      Bit#(TAdd#(PicHeightSz,10)) verTemp = zeroExtend(reqdata.ver) + zeroExtend(loadVerNum) + (yfracl==3&&(xfracl==1||xfracl==3)&&loadStage==1 ? 1 : 0);
      Bit#(13) mvhortemp = signExtend(reqdata.mvhor[13:2])-(horInter?2:0);
      Bit#(11) mvvertemp = signExtend(reqdata.mvver[11:2])-(verInter?2:0);
      if(mvhortemp[12]==1 && zeroExtend(0-mvhortemp)>horTemp)
	 begin
	    horAddr = 0;
	    horOut = 1;
	 end
      else
	 begin
	    horTemp = horTemp + signExtend(mvhortemp);
	    if(horTemp>=zeroExtend({picWidth,4'b0000}))
	       begin
		  horAddr = {picWidth-1,2'b11};
		  horOut = 1;
	       end
	    else
	       horAddr = truncate(horTemp>>2);
	 end
      if(mvvertemp[10]==1 && zeroExtend(0-mvvertemp)>verTemp)
	 verAddr = 0;
      else
	 begin
	    verTemp = verTemp + signExtend(mvvertemp);
	    if(verTemp>=zeroExtend({picHeight,4'b0000}))
	       verAddr = {picHeight-1,4'b1111};
	    else
	       verAddr = truncate(verTemp);
	 end
      memReqQ.enq(IPLoadLuma {refIdx:reqdata.refIdx,horOutOfBounds:horOut,hor:horAddr,ver:verAddr});
      Bool verFirst = twoStage || (yfracl==2&&(xfracl==1||xfracl==3));
      Bit#(2) loadHorNumMax = (reqdata.bt==IP8x8||reqdata.bt==IP8x4 ? 1 : 0) + (horInter ? 2 : (offset2==0 ? 0 : 1));
      Bit#(4) loadVerNumMax = (reqdata.bt==IP8x8||reqdata.bt==IP4x8 ? 7 : 3) + (verInter ? 5 : 0);
      if(verFirst)
	 begin
	    if(loadVerNum < loadVerNumMax)
	       loadVerNum <= loadVerNum+1;
	    else
	       begin
		  loadVerNum <= 0;
		  if(loadHorNum < loadHorNumMax)
		     begin
			if(loadStage == 1)
			   begin
			      offset = offset + (xfracl==3 ? 1 : 0);
			      if(!(offset==1 || (xfracl==3 && offset==2)))
				 loadHorNum <= loadHorNumMax;
			      else
				 begin
				    loadHorNum <= 0;
				    loadStage <= 0;
				    reqfifoLoad.deq();
				 end
			   end
			else
			   loadHorNum <= loadHorNum+1;
		     end
		  else
		     begin
			if(twoStage && loadStage==0)
			   begin
			      offset = offset + (xfracl==3 ? 1 : 0);
			      if((xfracl==3 ? offset<3 : offset<2))
				 loadHorNum <= 0;
			      else
				 loadHorNum <= loadHorNumMax+1;
			      loadStage <= 1;
			   end
			else
			   begin
			      loadHorNum <= 0;
			      loadStage <= 0;
			      reqfifoLoad.deq();
			   end
		     end
	       end
	 end
      else
	 begin
	    if(loadHorNum < loadHorNumMax)
	       loadHorNum <= loadHorNum+1;
	    else
	       begin
		  loadHorNum <= 0;
		  if(loadVerNum < loadVerNumMax)
		     loadVerNum <= loadVerNum+1;
		  else
		     begin
			loadVerNum <= 0;
			reqfifoLoad.deq();
		     end
	       end
	 end
      if(reqdata.bt==IP16x16 || reqdata.bt==IP16x8 || reqdata.bt==IP8x16)
	 $display( "ERROR Interpolation: loadLuma block sizes > 8x8 not supported");
      $display( "Trace interpolator: loadLuma %h %h %h %h %h %h %h", xfracl, yfracl, loadHorNum, loadVerNum, reqdata.refIdx, horAddr, verAddr);
   endrule   


   rule loadChroma( reqfifoLoad.first() matches tagged IPChroma .reqdata &&& !endOfFrameFlag );
      Bit#(3) xfracc = reqdata.mvhor[2:0];
      Bit#(3) yfracc = reqdata.mvver[2:0];
      Bit#(2) offset = reqdata.mvhor[4:3]+{reqdata.hor[0],1'b0};
      Bit#(1) horOut = 0;
      Bit#(TAdd#(PicWidthSz,1)) horAddr;
      Bit#(TAdd#(PicHeightSz,3)) verAddr;
      Bit#(TAdd#(PicWidthSz,11)) horTemp = zeroExtend({reqdata.hor,1'b0}) + zeroExtend({loadHorNum,2'b00});
      Bit#(TAdd#(PicHeightSz,9)) verTemp = zeroExtend(reqdata.ver) + zeroExtend(loadVerNum);
      if(reqdata.mvhor[13]==1 && zeroExtend(0-reqdata.mvhor[13:3])>horTemp)
	 begin
	    horAddr = 0;
	    horOut = 1;
	 end
      else
	 begin
	    horTemp = horTemp + signExtend(reqdata.mvhor[13:3]);
	    if(horTemp>=zeroExtend({picWidth,3'b000}))
	       begin
		  horAddr = {picWidth-1,1'b1};
		  horOut = 1;
	       end
	    else
	       horAddr = truncate(horTemp>>2);
	 end
      if(reqdata.mvver[11]==1 && zeroExtend(0-reqdata.mvver[11:3])>verTemp)
	 verAddr = 0;
      else
	 begin
	    verTemp = verTemp + signExtend(reqdata.mvver[11:3]);
	    if(verTemp>=zeroExtend({picHeight,3'b000}))
	       verAddr = {picHeight-1,3'b111};
	    else
	       verAddr = truncate(verTemp);
	 end
      memReqQ.enq(IPLoadChroma {refIdx:reqdata.refIdx,uv:reqdata.uv,horOutOfBounds:horOut,hor:horAddr,ver:verAddr});
      Bit#(2) loadHorNumMax = (reqdata.bt==IP4x8||reqdata.bt==IP4x4 ? (offset[1]==0||(xfracc==0&&offset!=3) ? 0 : 1) : ((reqdata.bt==IP16x16||reqdata.bt==IP16x8 ? 1 : 0) + (xfracc==0&&offset==0 ? 0 : 1)));
      Bit#(4) loadVerNumMax = (reqdata.bt==IP16x16||reqdata.bt==IP8x16 ? 7 : (reqdata.bt==IP16x8||reqdata.bt==IP8x8||reqdata.bt==IP4x8 ? 3 : 1)) + (yfracc==0 ? 0 : 1);
      if(loadHorNum < loadHorNumMax)
	 loadHorNum <= loadHorNum+1;
      else
	 begin
	    loadHorNum <= 0;
	    if(loadVerNum < loadVerNumMax)
	       loadVerNum <= loadVerNum+1;
	    else
	       begin
		  loadVerNum <= 0;
		  reqfifoLoad.deq();
	       end
	 end
      $display( "Trace interpolator: loadChroma %h %h %h %h %h %h %h", xfracc, yfracc, loadHorNum, loadVerNum, reqdata.refIdx, horAddr, verAddr);
   endrule
   

   rule work1Luma ( reqfifoWork1.first() matches tagged IPWLuma .reqdata &&& !work1Done );
      let xfracl = reqdata.xFracL;
      let yfracl = reqdata.yFracL;
      let offset = reqdata.offset;
      let blockT = reqdata.bt;
      Bool twoStage = (xfracl==1||xfracl==3) && (yfracl==1||yfracl==3);
      Vector#(20,Bit#(8)) work1Vector8Next = work1Vector8;
      if(memRespQ.first() matches tagged IPLoadResp .tempreaddata)
	 begin
	    memRespQ.deq();
	    Vector#(4,Bit#(8)) readdata = replicate(0);
	    readdata[0] = tempreaddata[7:0];
	    readdata[1] = tempreaddata[15:8];
	    readdata[2] = tempreaddata[23:16];
	    readdata[3] = tempreaddata[31:24];
	    //$display( "Trace interpolator: workLuma stage 0 readdata %h %h %h %h %h %h", workHorNum, workVerNum, readdata[3], readdata[2], readdata[1], readdata[0] );
	    Vector#(4,Bit#(8)) tempResult8 = replicate(0);
	    Vector#(4,Bit#(15)) tempResult15 = replicate(0);
	    if(xfracl==0 || yfracl==0 || xfracl==2)
	       begin
		  if(xfracl==0)//reorder
		     begin
			for(Integer ii=0; ii<4; ii=ii+1)
			   begin
			      Bit#(2) offsetplusii = offset+fromInteger(ii);
			      if(offset <= 3-fromInteger(ii) && offset!=0)
				 tempResult8[ii] = work1Vector8[offsetplusii];
			      else
				 tempResult8[ii] = readdata[offsetplusii];
			      work1Vector8Next[ii] = readdata[ii];
			   end
			for(Integer ii=0; ii<4; ii=ii+1)
			   tempResult15[ii] = zeroExtend({tempResult8[ii],5'b00000});
		     end
		  else//horizontal interpolation
		     begin
			offset = offset-2;
			for(Integer ii=0; ii<8; ii=ii+1)
			   work1Vector8Next[ii] = work1Vector8[ii+4];
			for(Integer ii=0; ii<4; ii=ii+1)
			   begin
			      Bit#(4) tempIndex = fromInteger(ii) + 8 - zeroExtend(offset);
			      work1Vector8Next[tempIndex] = readdata[ii];
			   end
			for(Integer ii=0; ii<4; ii=ii+1)
			   begin
			      tempResult15[ii] = interpolate8to15(work1Vector8Next[ii],work1Vector8Next[ii+1],work1Vector8Next[ii+2],work1Vector8Next[ii+3],work1Vector8Next[ii+4],work1Vector8Next[ii+5]);
			      tempResult8[ii] = clip1y10to8(truncate((tempResult15[ii]+16)>>5));
			      if(xfracl == 1)
				 tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,work1Vector8Next[ii+2]} + 1) >> 1);
			      else if(xfracl == 3)
				 tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,work1Vector8Next[ii+3]} + 1) >> 1);
			   end
		     end
		  Bit#(2) workHorNumOffset = (xfracl!=0 ? 2 : (reqdata.offset==0 ? 0 : 1));
		  if(work1HorNum >= workHorNumOffset)
		     begin
			Bit#(1) horAddr = truncate(work1HorNum-workHorNumOffset);
			if(yfracl == 0)
			   begin
			      for(Integer ii=0; ii<4; ii=ii+1)
				 tempResult15[ii] = zeroExtend({tempResult8[ii],5'b00000});
			   end
			workFile.upd({workFileFlag,work1VerNum,horAddr},tempResult15);
		     end
		  Bit#(2) workHorNumMax = (blockT==IP8x8||blockT==IP8x4 ? 1 : 0) + workHorNumOffset;
		  Bit#(4) workVerNumMax = (blockT==IP8x8||blockT==IP4x8 ? 7 : 3) + (yfracl!=0 ? 5 : 0);
		  if(work1HorNum < workHorNumMax)
		     work1HorNum <= work1HorNum+1;
		  else
		     begin
			work1HorNum <= 0;
			if(work1VerNum < workVerNumMax)
			   work1VerNum <= work1VerNum+1;
			else
			   begin
			      work1VerNum <= 0;
			      work1Done <= True;
			   end
		     end
	       end
	    else if(work1Stage == 0)//vertical interpolation
	       begin
		  offset = offset + (xfracl==3&&(yfracl==1||yfracl==3) ? 1 : 0);
		  for(Integer ii=0; ii<4; ii=ii+1)
		     tempResult15[ii] = interpolate8to15(work1Vector8[ii],work1Vector8[ii+4],work1Vector8[ii+8],work1Vector8[ii+12],work1Vector8[ii+16],readdata[ii]);
		  for(Integer ii=0; ii<16; ii=ii+1)
		     work1Vector8Next[ii] = work1Vector8[ii+4];
		  for(Integer ii=0; ii<4; ii=ii+1)
		     work1Vector8Next[ii+16] = readdata[ii];
		  Bit#(2) workHorNumMax = (blockT==IP8x8||blockT==IP8x4 ? 1 : 0) + (yfracl==2 ? 2 : (offset==0 ? 0 : 1));
		  Bit#(4) workVerNumMax = (blockT==IP8x8||blockT==IP4x8 ? 7 : 3) + 5;
		  Bit#(2) horAddr = work1HorNum;
		  Bit#(3) verAddr = truncate(work1VerNum-5);
		  if(work1VerNum > 4)
		     begin
			workFile.upd({workFileFlag,verAddr,horAddr},tempResult15);
			//$display( "Trace interpolator: workLuma stage 0 result %h %h %h %h %h %h %h", workHorNum, workVerNum, {verAddr,horAddr}, tempResult15[3], tempResult15[2], tempResult15[1], tempResult15[0]);
		     end
		  if(twoStage)
		     begin
			Bit#(2) storeHorAddr = work1HorNum;
			Bit#(4) storeVerAddr = work1VerNum;
			if((xfracl==3 ? offset<3 : offset<2))
			   storeHorAddr = storeHorAddr+1;
			if(yfracl==3)
			   storeVerAddr = storeVerAddr-3;
			else
			   storeVerAddr = storeVerAddr-2;
			if(storeVerAddr < 8)
			   storeFile.upd({workFileFlag,storeVerAddr[2:0],storeHorAddr},readdata);
		     end
		  if(work1VerNum < workVerNumMax)
		     work1VerNum <= work1VerNum+1;
		  else
		     begin
			work1VerNum <= 0;
			if(work1HorNum < workHorNumMax)
			   work1HorNum <= work1HorNum+1;
			else
			   begin
			      if(twoStage)
				 begin
				    work1Stage <= 1;
				    if((xfracl==3 ? offset<3 : offset<2))
				       work1HorNum <= 0;
				    else
				       work1HorNum <= workHorNumMax+1;
				 end
			      else
				 begin
				    work1HorNum <= 0;
				    work1Done <= True;
				 end
			   end
		     end
	       end
	    else//second stage of twoStage
	       begin
		  storeFile.upd({workFileFlag,work1VerNum[2:0],work1HorNum},readdata);
		  Bit#(2) workHorNumMax = (blockT==IP8x8||blockT==IP8x4 ? 1 : 0) + 2;
		  Bit#(4) workVerNumMax = (blockT==IP8x8||blockT==IP4x8 ? 7 : 3);
		  if(work1VerNum < workVerNumMax)
		     work1VerNum <= work1VerNum+1;
		  else
		     begin
			work1VerNum <= 0;
			offset = offset + (xfracl==3 ? 1 : 0);
			if(work1HorNum<workHorNumMax && !(offset==1 || (xfracl==3 && offset==2)))
			   work1HorNum <= workHorNumMax;
			else
			   begin
			      work1HorNum <= 0;
			      work1Stage <= 0;
			      work1Done <= True;
			   end
		     end
	       end		 
	 end
      work1Vector8 <= work1Vector8Next;
      $display( "Trace interpolator: work1Luma %h %h %h %h %h %h", xfracl, yfracl, work1HorNum, work1VerNum, offset, work1Stage);
   endrule


   rule work2Luma ( reqregWork2 matches tagged Valid .vdata &&& vdata matches tagged IPWLuma .reqdata &&& !work2Done &&& !work8x8Done );
      let xfracl = reqdata.xFracL;
      let yfracl = reqdata.yFracL;
      let offset = reqdata.offset;
      let blockT = reqdata.bt;
      Vector#(20,Bit#(8)) work2Vector8Next = work2Vector8;
      Vector#(20,Bit#(15)) work2Vector15Next = work2Vector15;
      Vector#(16,Bit#(1)) resultReadyNext = resultReady;
      Vector#(4,Bit#(8)) tempResult8 = replicate(0);
      Vector#(4,Bit#(15)) readdata = replicate(0);
      if(yfracl==0)
	 begin
	    readdata = workFile.sub({(1-workFileFlag),1'b0,work2VerNum[1],work2HorNum,work2VerNum[0]});
	    for(Integer ii=0; ii<4; ii=ii+1)
	       tempResult8[ii] = (readdata[ii])[12:5];
	    resultFile.upd({work2VerNum[1],work2HorNum,work2VerNum[0]},tempResult8);
	    resultReadyNext[{work2VerNum[1],work2HorNum,work2VerNum[0]}] = 1;
	    work2HorNum <= work2HorNum+1;
	    if(work2HorNum == 3)
	       begin
		  if(work2VerNum == 3)
		     begin
			work2VerNum <= 0;
			work2Done <= True;
			if(((blockT==IP4x8 || blockT==IP8x4) && work2SubMbPart==0) || (blockT==IP4x4 && work2SubMbPart<3))
			   work2SubMbPart <= work2SubMbPart+1;
			else
			   begin
			      work2SubMbPart <= 0;
			      work8x8Done <= True;
			   end
		     end
		  else
		     work2VerNum <= work2VerNum+1;
	       end
	 end
      else if(xfracl==0 || xfracl==2)//vertical interpolation
	 begin
	    readdata = workFile.sub({(1-workFileFlag),work2VerNum,work2HorNum[0]});
	    for(Integer ii=0; ii<4; ii=ii+1)
	       begin
		  tempResult8[ii] = interpolate15to8(work2Vector15[ii],work2Vector15[ii+4],work2Vector15[ii+8],work2Vector15[ii+12],work2Vector15[ii+16],readdata[ii]);
		  if(yfracl == 1)
		     tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,clip1y10to8(truncate((work2Vector15[ii+8]+16)>>5))} + 1) >> 1);
		  else if(yfracl == 3)
		     tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,clip1y10to8(truncate((work2Vector15[ii+12]+16)>>5))} + 1) >> 1);
	       end
	    for(Integer ii=0; ii<16; ii=ii+1)
	       work2Vector15Next[ii] = work2Vector15[ii+4];
	    for(Integer ii=0; ii<4; ii=ii+1)
	       work2Vector15Next[ii+16] = readdata[ii];
	    Bit#(2) workHorNumMax = 1;
	    Bit#(4) workVerNumMax = (blockT==IP8x8||blockT==IP4x8 ? 7 : 3) + 5;
	    if(work2VerNum > 4)				  
	       begin
		  Bit#(1) horAddr = truncate(work2HorNum);
		  Bit#(3) verAddr = truncate(work2VerNum-5);
		  horAddr = horAddr + ((blockT==IP4x8&&work2SubMbPart==1)||(blockT==IP4x4&&work2SubMbPart[0]==1) ? 1 : 0);
		  verAddr = verAddr + ((blockT==IP8x4&&work2SubMbPart==1)||(blockT==IP4x4&&work2SubMbPart[1]==1) ? 4 : 0);
		  resultFile.upd({verAddr,horAddr},tempResult8);
		  resultReadyNext[{verAddr,horAddr}] = 1;
	       end
	    if(work2VerNum < workVerNumMax)
	       work2VerNum <= work2VerNum+1;
	    else
	       begin
		  work2VerNum <= 0;
		  if(work2HorNum < workHorNumMax)
		     work2HorNum <= work2HorNum+1;
		  else
		     begin
			work2HorNum <= 0;
			work2Done <= True;
			if(((blockT==IP4x8 || blockT==IP8x4) && work2SubMbPart==0) || (blockT==IP4x4 && work2SubMbPart<3))
			   work2SubMbPart <= work2SubMbPart+1;
			else
			   begin
			      work2SubMbPart <= 0;
			      work8x8Done <= True;
			   end
		     end
	       end
	 end
      else//horizontal interpolation
	 begin
	    offset = offset-2;
	    if(yfracl == 2)
	       begin
		  readdata = workFile.sub({(1-workFileFlag),work2VerNum[2:0],work2HorNum});
		  for(Integer ii=0; ii<8; ii=ii+1)
		     work2Vector15Next[ii] = work2Vector15[ii+4];
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			Bit#(4) tempIndex = fromInteger(ii) + 8 - zeroExtend(offset);
			work2Vector15Next[tempIndex] = readdata[ii];
		     end
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			tempResult8[ii] = interpolate15to8(work2Vector15Next[ii],work2Vector15Next[ii+1],work2Vector15Next[ii+2],work2Vector15Next[ii+3],work2Vector15Next[ii+4],work2Vector15Next[ii+5]);
			if(xfracl == 1)
			   tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,clip1y10to8(truncate((work2Vector15Next[ii+2]+16)>>5))} + 1) >> 1);
			else if(xfracl == 3)
			   tempResult8[ii] = truncate(({1'b0,tempResult8[ii]} + {1'b0,clip1y10to8(truncate((work2Vector15Next[ii+3]+16)>>5))} + 1) >> 1);
		     end
	       end
	    else
	       begin
		  Vector#(4,Bit#(8)) readdata8 = storeFile.sub({(1-workFileFlag),work2VerNum[2:0],work2HorNum});
		  for(Integer ii=0; ii<8; ii=ii+1)
		     work2Vector8Next[ii] = work2Vector8[ii+4];
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			Bit#(4) tempIndex = fromInteger(ii) + 8 - zeroExtend(offset);
			work2Vector8Next[tempIndex] = readdata8[ii];
		     end
		  Vector#(4,Bit#(15)) tempResult15 = replicate(0);
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			tempResult15[ii] = interpolate8to15(work2Vector8Next[ii],work2Vector8Next[ii+1],work2Vector8Next[ii+2],work2Vector8Next[ii+3],work2Vector8Next[ii+4],work2Vector8Next[ii+5]);
			tempResult8[ii] = clip1y10to8(truncate((tempResult15[ii]+16)>>5));
		     end
		  Bit#(2) verOffset;
		  Vector#(4,Bit#(15)) verResult15 = replicate(0);
		  if(xfracl == 1)
		     verOffset = reqdata.offset;
		  else
		     verOffset = reqdata.offset+1;
		  readdata = workFile.sub({(1-workFileFlag),work2VerNum[2:0],(work2HorNum-2+(verOffset==0?0:1))});
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			Bit#(2) offsetplusii = verOffset+fromInteger(ii);
			if(verOffset <= 3-fromInteger(ii) && verOffset!=0)
			   verResult15[ii] = work2Vector15[offsetplusii];
			else
			   verResult15[ii] = readdata[offsetplusii];
			work2Vector15Next[ii] = readdata[ii];
		     end
		  for(Integer ii=0; ii<4; ii=ii+1)
		     begin
			Bit#(9) tempVal = zeroExtend(clip1y10to8(truncate((verResult15[ii]+16)>>5)));
			tempResult8[ii] = truncate((tempVal+zeroExtend(tempResult8[ii])+1)>>1);
		     end
	       end
	    if(work2HorNum >= 2)
	       begin
		  Bit#(1) horAddr = truncate(work2HorNum-2);
		  Bit#(3) verAddr = truncate(work2VerNum);
		  horAddr = horAddr + ((blockT==IP4x8&&work2SubMbPart==1)||(blockT==IP4x4&&work2SubMbPart[0]==1) ? 1 : 0);
		  verAddr = verAddr + ((blockT==IP8x4&&work2SubMbPart==1)||(blockT==IP4x4&&work2SubMbPart[1]==1) ? 4 : 0);
		  resultFile.upd({verAddr,horAddr},tempResult8);
		  resultReadyNext[{verAddr,horAddr}] = 1;
		  //$display( "Trace interpolator: workLuma stage 1 result %h %h %h %h %h %h %h %h", workHorNum, workVerNum, {verAddr,horAddr}, tempResult8[3], tempResult8[2], tempResult8[1], tempResult8[0], pack(resultReadyNext));
	       end
	    Bit#(2) workHorNumMax = (blockT==IP8x8||blockT==IP8x4 ? 1 : 0) + 2;
	    Bit#(4) workVerNumMax = (blockT==IP8x8||blockT==IP4x8 ? 7 : 3);
	    if(work2HorNum < workHorNumMax)
	       work2HorNum <= work2HorNum+1;
	    else
	       begin
		  work2HorNum <= 0;
		  if(work2VerNum < workVerNumMax)
		     work2VerNum <= work2VerNum+1;
		  else
		     begin
			work2VerNum <= 0;
			work2Done <= True;
			if(((blockT==IP4x8 || blockT==IP8x4) && work2SubMbPart==0) || (blockT==IP4x4 && work2SubMbPart<3))
			   work2SubMbPart <= work2SubMbPart+1;
			else
			   begin
			      work2SubMbPart <= 0;
			      work8x8Done <= True;
			   end
		     end
	       end
	 end
      work2Vector8 <= work2Vector8Next;
      work2Vector15 <= work2Vector15Next;
      resultReady <= resultReadyNext;
      $display( "Trace interpolator: work2Luma %h %h %h %h %h", xfracl, yfracl, work2HorNum, work2VerNum, offset);
   endrule


   rule work1Chroma ( reqfifoWork1.first() matches tagged IPWChroma .reqdata &&& !work1Done );
      Bit#(4) xfracc = zeroExtend(reqdata.xFracC);
      Bit#(4) yfracc = zeroExtend(reqdata.yFracC);
      let offset = reqdata.offset;
      let blockT = reqdata.bt;
      Vector#(20,Bit#(8)) work1Vector8Next = work1Vector8;
      if(memRespQ.first() matches tagged IPLoadResp .tempreaddata)
	 begin
	    memRespQ.deq();
	    Vector#(4,Bit#(8)) readdata = replicate(0);
	    readdata[0] = tempreaddata[7:0];
	    readdata[1] = tempreaddata[15:8];
	    readdata[2] = tempreaddata[23:16];
	    readdata[3] = tempreaddata[31:24];
	    Vector#(5,Bit#(8)) tempWork8 = replicate(0);
	    Vector#(5,Bit#(8)) tempPrev8 = replicate(0);
	    Vector#(4,Bit#(8)) tempResult8 = replicate(0);
	    Bool resultReadyFlag = False;
	    for(Integer ii=0; ii<4; ii=ii+1)
	       begin
		  Bit#(2) offsetplusii = offset+fromInteger(ii);
		  if(offset <= 3-fromInteger(ii) && !((blockT==IP4x8||blockT==IP4x4)&&(offset[1]==0||(xfracc==0&&offset!=3))) && !(xfracc==0&&offset==0))
		     tempWork8[ii] = work1Vector8[offsetplusii];
		  else
		     tempWork8[ii] = readdata[offsetplusii];
		  work1Vector8Next[ii] = readdata[ii];
	       end
	    tempWork8[4] = readdata[offset];
	    if((blockT==IP16x8 || blockT==IP16x16) && work1HorNum==(xfracc==0&&offset==0 ? 1 : 2))
	       begin
		  for(Integer ii=0; ii<5; ii=ii+1)
		     begin
			tempPrev8[ii] = work1Vector8[ii+9];
			work1Vector8Next[ii+9] = tempWork8[ii];
		     end
	       end
	    else
	       begin
		  for(Integer ii=0; ii<5; ii=ii+1)
		     tempPrev8[ii] = work1Vector8[ii+4];
		  if(work1HorNum==(xfracc==0&&offset==0 ? 0 : 1) || ((blockT==IP4x8||blockT==IP4x4)&&(offset[1]==0||(xfracc==0&&offset!=3))))
		     begin
			for(Integer ii=0; ii<5; ii=ii+1)
			   work1Vector8Next[ii+4] = tempWork8[ii];
		     end
	       end
	    if(yfracc==0)
	       begin
		  for(Integer ii=0; ii<5; ii=ii+1)
		     tempPrev8[ii] = tempWork8[ii];
	       end
	    for(Integer ii=0; ii<4; ii=ii+1)
	       begin
		  Bit#(14) tempVal = zeroExtend((8-xfracc))*zeroExtend((8-yfracc))*zeroExtend(tempPrev8[ii]);
		  tempVal = tempVal + zeroExtend(xfracc)*zeroExtend((8-yfracc))*zeroExtend(tempPrev8[ii+1]);
		  tempVal = tempVal + zeroExtend((8-xfracc))*zeroExtend(yfracc)*zeroExtend(tempWork8[ii]);
		  tempVal = tempVal + zeroExtend(xfracc)*zeroExtend(yfracc)*zeroExtend(tempWork8[ii+1]);
		  tempResult8[ii] = truncate((tempVal+32)>>6);
	       end
	    if(work1VerNum > 0 || yfracc==0)
	       begin
		  if(blockT==IP4x8 || blockT==IP4x4)
		     begin
			Bit#(5) tempIndex = 10 + zeroExtend(work1VerNum<<1);
			work1Vector8Next[tempIndex] = tempResult8[0];
			work1Vector8Next[tempIndex+1] = tempResult8[1];
			tempResult8[2] = tempResult8[0];
			tempResult8[3] = tempResult8[1];
			tempResult8[0] = work1Vector8[tempIndex];
			tempResult8[1] = work1Vector8[tempIndex+1];
			if((work1HorNum>0 || offset[1]==0) && work1SubMbPart[0]==1)
			   resultReadyFlag = True;
		     end
		  else
		     begin
			if(work1HorNum>0 || (xfracc==0 && offset==0))
			   resultReadyFlag = True;
		     end
	       end
	    if(resultReadyFlag)
	       begin
		  Bit#(1) horAddr = ((blockT==IP4x8 || blockT==IP4x4) ? 0 : truncate(((xfracc==0 && offset==0) ? work1HorNum : work1HorNum-1)));
		  Bit#(3) verAddr = truncate((yfracc==0 ? work1VerNum : work1VerNum-1));
		  horAddr = horAddr + ((blockT==IP16x8||blockT==IP16x16) ? 0 : work1MbPart[0]);
		  verAddr = verAddr + ((blockT==IP8x16||blockT==IP16x16) ? 0 : ((blockT==IP16x8) ? {work1MbPart[0],2'b00} : {work1MbPart[1],2'b00}));
		  verAddr = verAddr + ((blockT==IP8x4&&work1SubMbPart==1)||(blockT==IP4x4&&work1SubMbPart[1]==1) ? 2 : 0);
		  storeFile.upd({workFileFlag,1'b0,verAddr,horAddr},tempResult8);
	       end
	    Bit#(2) workHorNumMax = (blockT==IP4x8||blockT==IP4x4 ? (offset[1]==0||(xfracc==0&&offset!=3) ? 0 : 1) : ((blockT==IP16x16||blockT==IP16x8 ? 1 : 0) + (xfracc==0&&offset==0 ? 0 : 1)));
	    Bit#(4) workVerNumMax = (blockT==IP16x16||blockT==IP8x16 ? 7 : (blockT==IP16x8||blockT==IP8x8||blockT==IP4x8 ? 3 : 1)) + (yfracc==0 ? 0 : 1);
	    if(work1HorNum < workHorNumMax)
	       work1HorNum <= work1HorNum+1;
	    else
	       begin
		  work1HorNum <= 0;
		  if(work1VerNum < workVerNumMax)
		     work1VerNum <= work1VerNum+1;
		  else
		     begin
			Bool allDone = False;
			work1VerNum <= 0;
			if(((blockT==IP4x8 || blockT==IP8x4) && work1SubMbPart==0) || (blockT==IP4x4 && work1SubMbPart<3))
			   work1SubMbPart <= work1SubMbPart+1;
			else
			   begin
			      work1SubMbPart <= 0;
			      if(((blockT==IP16x8 || blockT==IP8x16) && work1MbPart==0) || (!(blockT==IP16x8 || blockT==IP8x16 || blockT==IP16x16) && work1MbPart<3))
				 work1MbPart <= work1MbPart+1;
			      else
				 begin
				    work1MbPart <= 0;
				    work1Done <= True;
				    allDone = True;
				 end
			   end
			if(!allDone)
			   reqfifoWork1.deq();
		     end
	       end
	 end
      work1Vector8 <= work1Vector8Next;
      $display( "Trace interpolator: work1Chroma %h %h %h %h %h", xfracc, yfracc, work1HorNum, work1VerNum, offset);
   endrule


   rule work2Chroma ( reqregWork2 matches tagged Valid .vdata &&& vdata matches tagged IPWChroma .reqdata &&& !work2Done &&& !work8x8Done );
      Vector#(16,Bit#(1)) resultReadyNext = resultReady;
      resultFile.upd({work2VerNum[1],work2HorNum,work2VerNum[0]},storeFile.sub({(1-workFileFlag),1'b0,work2VerNum[1],work2HorNum,work2VerNum[0]}));
      resultReadyNext[{work2VerNum[1],work2HorNum,work2VerNum[0]}] = 1;
      work2HorNum <= work2HorNum+1;
      if(work2HorNum == 3)
	 begin
	    if(work2VerNum == 3)
	       begin
		  work2VerNum <= 0;
		  work2Done <= True;
		  work8x8Done <= True;
	       end
	    else
	       work2VerNum <= work2VerNum+1;
	 end
      resultReady <= resultReadyNext;
      $display( "Trace interpolator: work2Chroma %h %h", work2HorNum, work2VerNum);
   endrule


  rule outputing( !outDone && resultReady[{outBlockNum[1],outPixelNum,outBlockNum[0]}]==1 );
      outfifo.enq(resultFile.sub({outBlockNum[1],outPixelNum,outBlockNum[0]}));
      outPixelNum <= outPixelNum+1;
      if(outPixelNum == 3)
	 begin
	    outBlockNum <= outBlockNum+1;
	    if(outBlockNum == 3)
	       outDone <= True;
	 end
      $display( "Trace interpolator: outputing %h %h", outBlockNum, outPixelNum);
   endrule


   rule switching( work1Done && (work2Done || reqregWork2==Invalid) && !work8x8Done);
      work1Done <= False;
      work2Done <= False;
      reqregWork2 <= (tagged Valid reqfifoWork1.first());
      workFileFlag <= 1-workFileFlag;
      reqfifoWork1.deq();
      $display( "Trace interpolator: switching %h %h", outBlockNum, outPixelNum);
   endrule
   

   rule switching8x8( work1Done && (work2Done || reqregWork2==Invalid) && work8x8Done && outDone);
      outDone <= False;
      work8x8Done <= False;
      resultReady <= replicate(0);
      work1Done <= False;
      work2Done <= False;
      reqregWork2 <= (tagged Valid reqfifoWork1.first());
      workFileFlag <= 1-workFileFlag;
      reqfifoWork1.deq();
      $display( "Trace interpolator: switching8x8 %h %h", outBlockNum, outPixelNum);
   endrule



   method Action   setPicWidth( Bit#(PicWidthSz) newPicWidth );
      picWidth <= newPicWidth;
   endmethod
   
   method Action   setPicHeight( Bit#(PicHeightSz) newPicHeight );
      picHeight <= newPicHeight;
   endmethod
   
   method Action request( InterpolatorIT inputdata );
      reqfifoLoad.enq(inputdata);
      if(inputdata matches tagged IPLuma .indata)
	 reqfifoWork1.enq(IPWLuma {xFracL:indata.mvhor[1:0],yFracL:indata.mvver[1:0],offset:indata.mvhor[3:2],bt:indata.bt});
      else if(inputdata matches tagged IPChroma .indata)
	 reqfifoWork1.enq(IPWChroma {xFracC:indata.mvhor[2:0],yFracC:indata.mvver[2:0],offset:indata.mvhor[4:3]+{indata.hor[0],1'b0},bt:indata.bt});
   endmethod

   method Vector#(4,Bit#(8)) first();
      return outfifo.first();
   endmethod
   
   method Action deq();
      outfifo.deq();
   endmethod
   
   method Action endOfFrame();
      endOfFrameFlag <= True;
   endmethod
   
   interface Client mem_client;
      interface Get request  = fifoToGet(memReqQ);
      interface Put response = fifoToPut(memRespQ);
   endinterface


endmodule


endpackage
