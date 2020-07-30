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
// Inverse Quantizer and Inverse Transformer implementation
//----------------------------------------------------------------------
//
//

package mkInverseTrans;

import H264Types::*;

import IInverseTrans::*;
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
 void     Start;            //not working on anything in particular
 void     Intra16x16DC;
 void     Intra16x16;
 void     ChromaDC;
 void     Chroma;
 void     Regular4x4;
}
State deriving(Eq,Bits);

typedef union tagged                
{
 void     Passing;          //not working on anything in particular
 void     LoadingDC;
 void     Scaling;          //does not include scaling for DC (just loading in that case)
 void     TransformingDC;
 void     ScalingDC;
}
Process deriving(Eq,Bits);

typedef union tagged                
{
 void     Invalid;
 void     Zeros;
 Vector#(16,Bit#(16)) Values;
}
PipeType deriving(Eq,Bits);

      
//-----------------------------------------------------------
// Helper functions

function Bit#(6) qpi_to_qpc( Bit#(6) qpi );//mapping from qpi to qpc
   case ( qpi )
      30: return 29;
      31: return 30;
      32: return 31;
      33: return 32;
      34: return 32;
      35: return 33;
      36: return 34;
      37: return 34;
      38: return 35;
      39: return 35;
      40: return 36;
      41: return 36;
      42: return 37;
      43: return 37;
      44: return 37;
      45: return 38;
      46: return 38;
      47: return 38;
      48: return 39;
      49: return 39;
      50: return 39;
      51: return 39;
      default: return qpi;
   endcase
endfunction


function Bit#(4) reverseInverseZigZagScan( Bit#(4) idx );
   case ( idx )
      0: return 15;
      1: return 14;
      2: return 11;
      3: return 7;
      4: return 10;
      5: return 13;
      6: return 12;
      7: return 9;
      8: return 6;
      9: return 3;
      10: return 2;
      11: return 5;
      12: return 8;
      13: return 4;
      14: return 1;
      15: return 0;
   endcase
endfunction


function Tuple2#(Bit#(4),Bit#(3)) qpdivmod6( Bit#(6) qp );
   Bit#(6) tempqp = qp;
   Bit#(4) tempdiv = 0;
   for(Integer ii=5; ii>=2; ii=ii-1)
      begin
	 if(tempqp >= (6'b000011 << (fromInteger(ii)-1)))
	    begin
	       tempqp = tempqp - (6'b000011 << (fromInteger(ii)-1));
	       tempdiv = tempdiv | (4'b0001 << (fromInteger(ii)-2));
	    end
      end
   return tuple2(tempdiv,truncate(tempqp));
endfunction


function Vector#(4,Bit#(16)) dcTransFunc( Bit#(16) in0, Bit#(16) in1, Bit#(16) in2, Bit#(16) in3 );
   Vector#(4,Bit#(16)) resultVector = replicate(0);
   resultVector[0] = in0 + in1 + in2 + in3;
   resultVector[1] = in0 + in1 - in2 - in3;
   resultVector[2] = in0 - in1 - in2 + in3;
   resultVector[3] = in0 - in1 + in2 - in3;
   return resultVector;
endfunction


function Vector#(4,Bit#(16)) transFunc( Bit#(16) in0, Bit#(16) in1, Bit#(16) in2, Bit#(16) in3 );
   Vector#(4,Bit#(16)) resultVector = replicate(0);
   Bit#(16) workValue0 = in0 + in2;
   Bit#(16) workValue1 = in0 - in2;
   Bit#(16) workValue2 = signedShiftRight(in1,1) - in3;
   Bit#(16) workValue3 = in1 + signedShiftRight(in3,1);
   resultVector[0] = workValue0 + workValue3;
   resultVector[1] = workValue1 + workValue2;
   resultVector[2] = workValue1 - workValue2;
   resultVector[3] = workValue0 - workValue3;
   return resultVector;
endfunction


//-----------------------------------------------------------
// Inverse Quantizer and Inverse Transformer Module
//-----------------------------------------------------------


(* synthesize *)
module mkInverseTrans( IInverseTrans );

   FIFO#(EntropyDecOT_InverseTrans) infifo  <- mkSizedFIFO(inverseTrans_infifo_size);
   FIFO#(InverseTransOT)            outfifo <- mkFIFO;
   Reg#(Bit#(4))       blockNum <- mkReg(0);
   Reg#(Bit#(4))       pixelNum <- mkReg(0);//also used as a regular counter during inverse transformation
   Reg#(State)         state    <- mkReg(Start);
   Reg#(Process)       process  <- mkReg(Passing);

   Reg#(Bit#(5))        chroma_qp_index_offset <- mkReg(0);
   Reg#(Bit#(6))        ppspic_init_qp <- mkReg(0);
   Reg#(Bit#(6))        slice_qp       <- mkReg(0);
   Reg#(Bit#(6))        qpy            <- mkReg(0);//Calculating it requires 8 bits, but value only 0 to 51
   Reg#(Bit#(6))        qpc            <- mkReg(0);
   Reg#(Bit#(3))        qpymod6        <- mkReg(0);
   Reg#(Bit#(3))        qpcmod6        <- mkReg(0);
   Reg#(Bit#(4))        qpydiv6        <- mkReg(0);
   Reg#(Bit#(4))        qpcdiv6        <- mkReg(0);

   Reg#(Vector#(16,Bit#(16))) storeVector <- mkRegU();
   Reg#(Vector#(16,Bit#(16))) workVector  <- mkRegU();
   Reg#(PipeType)             work2Vector <- mkReg(Invalid);
   Reg#(PipeType)             work3Vector <- mkReg(Invalid);
   Reg#(Bool)                 stage1Zeros <- mkReg(False);
   Reg#(Bool)                 stage1Done  <- mkReg(False);
   Reg#(Bool)                 stage2Done  <- mkReg(False);
   Reg#(Bool)                 stage3Done  <- mkReg(False);
   Reg#(Bit#(3))              stage2Step  <- mkReg(0);
   Reg#(Bit#(2))              stage3Step  <- mkReg(0);

   

   //-----------------------------------------------------------
   // Rules

   
   rule passing (process==Passing && work2Vector==Invalid && (stage3Done || work3Vector==Invalid) );
      //$display( "Trace Inverse Trans: passing infifo packed %h", pack(infifo.first()));
      case (infifo.first()) matches
	 tagged NewUnit . xdata :
	    begin
	       infifo.deq();
	       $display("ccl3newunit");
	       $display("ccl3rbspbyte %h", xdata);
	    end
	 tagged SDMmbtype .xdata :
	    begin
	       infifo.deq();
	       $display( "INFO InverseTrans: SDMmbtype %0d", xdata);
	       if(mbPartPredMode(xdata,0) == Intra_16x16)
		  state <= Intra16x16DC;
	       else
		  state <= Regular4x4;
	    end
	 tagged PPSpic_init_qp .xdata :
	    begin
	       infifo.deq();
	       ppspic_init_qp <= truncate(xdata);
	    end
	 tagged SHslice_qp_delta .xdata :
	    begin
	       infifo.deq();
	       slice_qp <= ppspic_init_qp+truncate(xdata);
	       Bit#(6) qpynext = ppspic_init_qp+truncate(xdata);
	       qpy <= qpynext;
	       Bit#(7) qpitemp = zeroExtend(chroma_qp_index_offset+12) + zeroExtend(qpynext);
	       Bit#(6) qpi;
	       if(qpitemp < 12)
		  qpi = 0;
	       else if(qpitemp > 63)
		  qpi = 51;
	       else
		  qpi = truncate(qpitemp-12);
	       qpc <= qpi_to_qpc(qpi);
	       outfifo.enq(IBTmb_qp {qpy:qpynext,qpc:qpi_to_qpc(qpi)});
	    end
	 tagged SDMmb_qp_delta .xdata :
	    begin
	       infifo.deq();
	       Bit#(8) qpytemp = zeroExtend(qpy) + zeroExtend(xdata+52);
	       Bit#(6) qpynext;
	       if(qpytemp >= 104)
		  qpynext = truncate(qpytemp - 104);
	       else if(qpytemp >= 52)
		  qpynext = truncate(qpytemp - 52);
	       else
		  qpynext = truncate(qpytemp);
	       qpy <= qpynext;
	       
	       //$display( "TRACE InverseTrans: qpy %0d", qpynext );
	       //$display( "TRACE InverseTrans: qpy %0d", qpynext );
	       Tuple2#(Bit#(4),Bit#(3)) temptuple = qpdivmod6(qpynext);
	       qpydiv6 <= tpl_1(temptuple);
	       qpymod6 <= tpl_2(temptuple);
	       //$display( "TRACE InverseTrans: qpydiv6 %0d", tpl_1(temptuple) );
	       //$display( "TRACE InverseTrans: qpymod6 %0d", tpl_2(temptuple) );

	       Bit#(7) qpitemp = zeroExtend(chroma_qp_index_offset+12) + zeroExtend(qpynext);
	       Bit#(6) qpi;
	       if(qpitemp < 12)
		  qpi = 0;
	       else if(qpitemp > 63)
		  qpi = 51;
	       else
		  qpi = truncate(qpitemp-12);
	       qpc <= qpi_to_qpc(qpi);
	       outfifo.enq(IBTmb_qp {qpy:qpynext,qpc:qpi_to_qpc(qpi)});
	    end
	 tagged PPSchroma_qp_index_offset .xdata :
	    begin
	       infifo.deq();
	       chroma_qp_index_offset <= xdata;
	    end
	 tagged SDMRcoeffLevelPlusZeros .xdata :
	    begin
	       blockNum <= 0;
	       pixelNum <= 0;
	       if(state == Intra16x16DC)
		  begin
		     $display( "INFO InverseTrans: 16x16 MB" );
		     process <= LoadingDC;
		  end
	       else
		  begin
		     $display( "INFO InverseTrans: Non-16x16 MB" );
		     process <= Scaling;
		  end
	       workVector <= replicate(0);
	       Tuple2#(Bit#(4),Bit#(3)) temptuple = qpdivmod6(qpc);
	       qpcdiv6 <= tpl_1(temptuple);
	       qpcmod6 <= tpl_2(temptuple);
	    end
	 tagged SDMRcoeffLevelZeros .xdata :
	    begin
	       blockNum <= 0;
	       pixelNum <= 0;
	       if(state == Intra16x16DC)
		  begin
		     $display( "INFO InverseTrans: 16x16 MB" );
		     process <= LoadingDC;
		  end
	       else
		  begin
		     $display( "INFO InverseTrans: Non-16x16 MB" );
		     process <= Scaling;
		  end
	       workVector <= replicate(0);
	       Tuple2#(Bit#(4),Bit#(3)) temptuple = qpdivmod6(qpc);
	       qpcdiv6 <= tpl_1(temptuple);
	       qpcmod6 <= tpl_2(temptuple);
	    end
	 default: infifo.deq();
      endcase
   endrule


   rule loadingDC (process matches LoadingDC);
      Vector#(16,Bit#(16)) workVectorTemp = workVector;

      case (infifo.first()) matches
	 tagged SDMRcoeffLevelZeros .xdata :
	    begin
	       infifo.deq();
	       pixelNum <= pixelNum+truncate(xdata);
	       if((state==ChromaDC && zeroExtend(pixelNum)+xdata==8) || zeroExtend(pixelNum)+xdata==16)
		  process <= TransformingDC;
	       else if((state==ChromaDC && zeroExtend(pixelNum)+xdata>8) || zeroExtend(pixelNum)+xdata>16)
		  $display( "ERROR InverseTrans: loadingDC index overflow" );
	    end
	 tagged SDMRcoeffLevelPlusZeros .xdata :
	    begin
	       infifo.deq();
	       Bit#(16) workValue = signExtend(xdata.level);
	       if(state==ChromaDC)
		  begin
		     if(pixelNum<4)
			workVector <= update(workVectorTemp, 3-pixelNum, workValue);
		     else
			workVector <= update(workVectorTemp, 11-pixelNum, workValue);
		  end
	       else
		  workVector <= update(workVectorTemp, reverseInverseZigZagScan(pixelNum), workValue);
	       pixelNum <= pixelNum+1+truncate(xdata.zeros);
	       if((state==ChromaDC && zeroExtend(pixelNum)+1+xdata.zeros==8) || zeroExtend(pixelNum)+1+xdata.zeros==16)
		  process <= TransformingDC;
	       else if((state==ChromaDC && zeroExtend(pixelNum)+1+xdata.zeros>8) || zeroExtend(pixelNum)+1+xdata.zeros>16)
		  $display( "ERROR InverseTrans: loadingDC index overflow" );
	    end
	 default: process <= Passing;
      endcase
   endrule


   rule transformingDC (process matches TransformingDC);
      Vector#(16,Bit#(16)) workVectorTemp = workVector;
      Vector#(16,Bit#(16)) workVectorNew = workVector;
      Vector#(16,Bit#(16)) storeVectorTemp = storeVector;

      if(state == ChromaDC)
	 begin
	    case ( pixelNum )
	       8:
	       begin
		  workVectorNew[0] = workVectorTemp[0] + workVectorTemp[2];
		  workVectorNew[1] = workVectorTemp[1] + workVectorTemp[3];
		  workVectorNew[2] = workVectorTemp[0] - workVectorTemp[2];
		  workVectorNew[3] = workVectorTemp[1] - workVectorTemp[3];
		  pixelNum <= pixelNum+1;
	       end
	       9:
	       begin
		  workVectorNew[0] = workVectorTemp[0] + workVectorTemp[1];
		  workVectorNew[1] = workVectorTemp[0] - workVectorTemp[1];
		  workVectorNew[2] = workVectorTemp[2] + workVectorTemp[3];
		  workVectorNew[3] = workVectorTemp[2] - workVectorTemp[3];
		  pixelNum <= pixelNum+1;
	       end
	       10:
	       begin
		  workVectorNew[4] = workVectorTemp[4] + workVectorTemp[6];
		  workVectorNew[5] = workVectorTemp[5] + workVectorTemp[7];
		  workVectorNew[6] = workVectorTemp[4] - workVectorTemp[6];
		  workVectorNew[7] = workVectorTemp[5] - workVectorTemp[7];
		  pixelNum <= pixelNum+1;
	       end
	       11:
	       begin
		  workVectorNew[4] = workVectorTemp[4] + workVectorTemp[5];
		  workVectorNew[5] = workVectorTemp[4] - workVectorTemp[5];
		  workVectorNew[6] = workVectorTemp[6] + workVectorTemp[7];
		  workVectorNew[7] = workVectorTemp[6] - workVectorTemp[7];
		  pixelNum <= 0;
		  process <= ScalingDC;
	       end
	       default:
	          $display( "ERROR InverseTrans: transformingDC ChromaDC unexpected pixelNum" );
	    endcase
	    workVector <= workVectorNew;
	 end
      else if(state == Intra16x16DC)
	 begin
	    Vector#(4,Bit#(16)) resultVector = replicate(0);
	    if(pixelNum < 4)
	       begin
		  Bit#(4) tempIndex = zeroExtend(pixelNum[1:0]);
		  resultVector = dcTransFunc( workVectorTemp[tempIndex], workVectorTemp[tempIndex+4], workVectorTemp[tempIndex+8], workVectorTemp[tempIndex+12] );
		  for(Integer ii=0; ii<4; ii=ii+1)
		     workVectorNew[tempIndex+fromInteger(ii*4)] = resultVector[ii];
	       end
	    else if(pixelNum < 8)
	       begin
		  Bit#(4) tempIndex = {pixelNum[1:0],2'b00};
		  resultVector = dcTransFunc( workVectorTemp[tempIndex], workVectorTemp[tempIndex+1], workVectorTemp[tempIndex+2], workVectorTemp[tempIndex+3] );
		  for(Integer ii=0; ii<4; ii=ii+1)
		     workVectorNew[tempIndex+fromInteger(ii)] = resultVector[ii];
	       end
	    else
	       $display( "ERROR InverseTrans: transforming Intra16x16DC unexpected pixelNum" );
	    workVector <= workVectorNew;
	    if(pixelNum == 7)
	       begin
		  pixelNum <= 0;
		  process <= ScalingDC;
	       end
	    else
	       pixelNum <= pixelNum+1;
	 end
      else
	 $display( "ERROR InverseTrans: transformingDC unexpected state" );
   endrule

   
   rule scalingDC (process matches ScalingDC);
      Bit#(6)  qp;
      Bit#(4)  qpdiv6;
      Bit#(3)  qpmod6;
      Bit#(6)  workOne = 1;
      Bit#(16) workValue;
      Bit#(22) storeValueTemp;
      Bit#(16) storeValue;
      Vector#(16,Bit#(16)) workVectorTemp = workVector;
      Vector#(16,Bit#(16)) storeVectorTemp = storeVector;

      if(state==ChromaDC)
	 begin
	    qp = qpc;
	    qpdiv6 = qpcdiv6;
	    qpmod6 = qpcmod6;
	 end
      else
	 begin
	    qp = qpy;
	    qpdiv6 = qpydiv6;
	    qpmod6 = qpymod6;
	 end
      workValue = select(workVectorTemp, pixelNum);
      Bit#(5) levelScaleValue=0;
      case(qpmod6)
	 0: levelScaleValue = 10;
	 1: levelScaleValue = 11;
	 2: levelScaleValue = 13;
	 3: levelScaleValue = 14;
	 4: levelScaleValue = 16;
	 5: levelScaleValue = 18;
	 default: $display( "ERROR InverseTrans: scalingDC levelScaleGen case default" );
      endcase
      storeValueTemp = zeroExtend(levelScaleValue)*signExtend(workValue);
      if(state==ChromaDC)
	 storeValue = truncate( (storeValueTemp << qpdiv6) >> 1 );
      else
	 begin
	    if(qp >= 36)
	       storeValue = truncate( storeValueTemp << (qpdiv6 - 2) );
	    else
	       storeValue = truncate( ((storeValueTemp << 4) + zeroExtend(workOne << (5-qpdiv6))) >> (6 - qpdiv6) );
	 end
      storeVector <= update(storeVectorTemp, pixelNum, storeValue);
      if((state==ChromaDC && pixelNum==7) || pixelNum==15)
	 begin
	    blockNum <= 0;
	    pixelNum <= 0;
	    workVector <= replicate(0);
	    if(state==ChromaDC)
	       state <= Chroma;
	    else
	       state <= Intra16x16;
	    process <= Scaling;
	 end
      else if((state==ChromaDC && pixelNum>7) || pixelNum>15)
	 $display( "ERROR InverseTrans: scalingDC index overflow" );
      else
	 pixelNum <= pixelNum+1;
   endrule


   rule switching ( (stage1Done && work2Vector==Invalid) || (stage2Done && (stage3Done || work3Vector==Invalid)) );
      Bool switch2to3 = False;
      if(stage2Done && (stage3Done || work3Vector==Invalid))
	 begin
	    switch2to3 = True;
	    work3Vector <= work2Vector;
	    stage3Done <= False;
	 end
      if(stage1Done && (switch2to3 || work2Vector==Invalid))
	 begin
	    Vector#(16,Bit#(16)) workVectorTemp = workVector;
	    if(state==Intra16x16)
	       workVectorTemp[0] = storeVector[{blockNum[3],blockNum[1],blockNum[2],blockNum[0]}];
	    else if(state==Chroma)
	       workVectorTemp[0] = storeVector[blockNum];
	    if(stage1Zeros)
	       work2Vector <= Zeros;
	    else
	       work2Vector <= (tagged Values workVectorTemp);
	    stage1Zeros <= False;
	    stage1Done <= False;
	    workVector <= replicate(0);
	    if(state==Chroma)
	       begin
		  if(blockNum<7)
		     blockNum <= blockNum+1;
		  else if (blockNum==7)
		     begin
			blockNum <= 0;
			process <= Passing;
		     end
		  else
		     $display( "ERROR InverseTrans: switching chroma unexpected blockNum" );
	       end
	    else
	       begin
		  blockNum <= blockNum+1;
		  if(blockNum==15)
		     begin
			state <= ChromaDC;
			process <= LoadingDC;
		     end
		  else
		     process <= Scaling;
	       end
	 end
      else //switch2to3==True
	 work2Vector <= Invalid;
      stage2Done <= False;
   endrule


   rule scaling (process==Scaling && !stage1Done );
      Vector#(16,Bit#(16)) workVectorTemp = workVector;
      Vector#(16,Bit#(16)) storeVectorTemp = storeVector;

      case (infifo.first()) matches
	 tagged SDMRcoeffLevelZeros .xdata :
	    begin
	       infifo.deq();
	       if(zeroExtend(pixelNum)+xdata==16 || (zeroExtend(pixelNum)+xdata==15 && (state==Chroma || state==Intra16x16)))
		  begin
		     Bit#(16) prevValue0=0;
		     if(state==Intra16x16)
			prevValue0 = select(storeVectorTemp, {blockNum[3],blockNum[1],blockNum[2],blockNum[0]});
		     else if(state==Chroma)
			prevValue0 = select(storeVectorTemp, blockNum);
		     if(xdata==16 || (xdata==15 && (state==Chroma || state==Intra16x16) && prevValue0==0))
			stage1Zeros <= True;
		     stage1Done <= True;
		     pixelNum <= 0;
		  end
	       else if(zeroExtend(pixelNum)+xdata>16 || (zeroExtend(pixelNum)+xdata>15 && (state==Chroma || state==Intra16x16)))
		  $display( "ERROR InverseTrans: scaling index overflow" );
	       else
		  pixelNum <= pixelNum+truncate(xdata);
	       //$display( "TRACE InverseTrans: coeff zeros %0d", xdata );
	    end
	 tagged SDMRcoeffLevelPlusZeros .xdata :
	    begin
	       infifo.deq();
	       Bit#(6)  qp;
	       Bit#(4)  qpdiv6;
	       Bit#(3)  qpmod6;
	       if(state==Chroma)
		  begin
		     qp = qpc;
		     qpdiv6 = qpcdiv6;
		     qpmod6 = qpcmod6;
		  end
	       else
		  begin
		     qp = qpy;
		     qpdiv6 = qpydiv6;
		     qpmod6 = qpymod6;
		  end
	       Bit#(5) levelScaleValue=0;
	       if(pixelNum==15 || pixelNum==12 || pixelNum==10 || pixelNum==4)
		  begin
		     case(qpmod6)
			0: levelScaleValue = 10;
			1: levelScaleValue = 11;
			2: levelScaleValue = 13;
			3: levelScaleValue = 14;
			4: levelScaleValue = 16;
			5: levelScaleValue = 18;
			default: $display( "ERROR InverseTrans: levelScaleGen case default" );
		     endcase
		  end
	       else if(pixelNum==11 || pixelNum==5 || pixelNum==3 || pixelNum==0)
		  begin
		     case(qpmod6)
			0: levelScaleValue = 16;
			1: levelScaleValue = 18;
			2: levelScaleValue = 20;
			3: levelScaleValue = 23;
			4: levelScaleValue = 25;
			5: levelScaleValue = 29;
			default: $display( "ERROR InverseTrans: levelScaleGen case default" );
		     endcase
		  end
	       else
		  begin
		     case(qpmod6)
			0: levelScaleValue = 13;
			1: levelScaleValue = 14;
			2: levelScaleValue = 16;
			3: levelScaleValue = 18;
			4: levelScaleValue = 20;
			5: levelScaleValue = 23;
			default: $display( "ERROR InverseTrans: levelScaleGen case default" );
		     endcase
		  end
	       Bit#(16) workValueTemp = zeroExtend(levelScaleValue)*signExtend(xdata.level);
	       Bit#(16) workValue;
	       workValue = workValueTemp << qpdiv6;
	       workVector <= update(workVectorTemp, reverseInverseZigZagScan(pixelNum), workValue);
	       if(zeroExtend(pixelNum)+1+xdata.zeros==16 || (zeroExtend(pixelNum)+1+xdata.zeros==15 && (state==Chroma || state==Intra16x16)))
		  begin
		     stage1Done <= True;
		     pixelNum <= 0;
		  end
	       else if(zeroExtend(pixelNum)+1+xdata.zeros>16 || (zeroExtend(pixelNum)+1+xdata.zeros>15 && (state==Chroma || state==Intra16x16)))
		  $display( "ERROR InverseTrans: scaling index overflow" );
	       else
		  pixelNum <= pixelNum+1+truncate(xdata.zeros);
	    end
	 default: process <= Passing;
      endcase
   endrule


   rule transforming ( work2Vector!=Invalid && !stage2Done );
      if(work2Vector matches tagged Values .xdata)
	 begin
	    Vector#(16,Bit#(16)) work2VectorNew = xdata;
	    if(stage2Step < 4)
	       begin
		  Bit#(4) tempIndex = {stage2Step[1:0],2'b00};
		  Vector#(4,Bit#(16)) resultVector = transFunc( xdata[tempIndex], xdata[tempIndex+1], xdata[tempIndex+2], xdata[tempIndex+3] );
		  for(Integer ii=0; ii<4; ii=ii+1)
		     work2VectorNew[tempIndex+fromInteger(ii)] = resultVector[ii];
	       end
	    else
	       begin
		  Bit#(4) tempIndex = zeroExtend(stage2Step[1:0]);
		  Vector#(4,Bit#(16)) resultVector = transFunc( xdata[tempIndex], xdata[tempIndex+4], xdata[tempIndex+8], xdata[tempIndex+12] );
		  for(Integer ii=0; ii<4; ii=ii+1)
		     work2VectorNew[tempIndex+fromInteger(ii*4)] = resultVector[ii];
	       end
	    work2Vector <= (tagged Values work2VectorNew);
	    if(stage2Step == 7)
	       stage2Done <= True;
	    stage2Step <= stage2Step+1;
	 end
      else //All Zeros
	 stage2Done <= True;
   endrule


   rule outputing ( work3Vector!=Invalid && !stage3Done );
      if(work3Vector matches tagged Values .xdata)
	 begin
	    Vector#(4,Bit#(10)) outputVector = replicate(0);
	    for(Integer ii=0; ii<4; ii=ii+1)
	       outputVector[ii] = truncate((xdata[{stage3Step,2'b00}+fromInteger(ii)]+32) >> 6);
	    outfifo.enq(tagged ITBresidual outputVector);
	    Int#(10) tempint = unpack(outputVector[0]);
	    $display("ccl3IBTresidual %0d", tempint);
	    tempint = unpack(outputVector[1]);
	    $display("ccl3IBTresidual %0d", tempint);
	    tempint = unpack(outputVector[2]);
	    $display("ccl3IBTresidual %0d", tempint);
	    tempint = unpack(outputVector[3]);
	    $display("ccl3IBTresidual %0d", tempint);
	    if(stage3Step == 3)
	       stage3Done <= True;
	    stage3Step <= stage3Step+1;
	 end
      else
	 begin
	    outfifo.enq(ITBcoeffLevelZeros);
	    stage3Done <= True;
	 end
   endrule



   interface Put ioin  = fifoToPut(infifo);
   interface Get ioout = fifoToGet(outfifo);

      
endmodule

endpackage
