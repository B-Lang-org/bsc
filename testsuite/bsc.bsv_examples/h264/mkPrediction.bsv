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
// Prediction
//----------------------------------------------------------------------
//
//

package mkPrediction;

import H264Types::*;

import IPrediction::*;
import IInterpolator::*;
import mkInterpolator::*;
import FIFO::*;
import FIFOF::*;
import Vector::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;


//-----------------------------------------------------------
// Local Datatypes
//-----------------------------------------------------------

typedef union tagged                
{
 void     Intra;            //Intra non-4x4
 void     Intra4x4;
 void     Inter;
}
OutState deriving(Eq,Bits);

typedef union tagged                
{
 void     Start;            //not working on anything in particular
 void     Intra16x16;
 void     Intra4x4;
 void     IntraPCM;
}
IntraState deriving(Eq,Bits);

typedef union tagged                
{
 void     Start;            //not working on anything in particular
 void     InterP16x16;
 void     InterP16x8;
 void     InterP8x16;
 void     InterP8x8;
 void     InterP8x8ref0;
 void     InterPskip;
}
InterState deriving(Eq,Bits);

typedef union tagged
{
 Bit#(1) NotInter;//0 for not available, 1 for intra-coded
 struct {Bit#(4) refIdx; Bit#(14) mvhor; Bit#(12) mvver; Bit#(1) nonZeroTransCoeff;} BlockMv;
}
InterBlockMv deriving(Eq,Bits);

typedef union tagged
{
 void SkipMB;
 void NonSkipMB;
 void Intra4x4;
 void Intra4x4PlusChroma;
}
NextOutput deriving(Eq,Bits);


      
//-----------------------------------------------------------
// Helper functions

function Bit#(8) intra4x4SelectTop( Bit#(72) valVector, Bit#(4) idx );
   case(idx)
      0: return valVector[15:8];
      1: return valVector[23:16];
      2: return valVector[31:24];
      3: return valVector[39:32];
      4: return valVector[47:40];
      5: return valVector[55:48];
      6: return valVector[63:56];
      7: return valVector[71:64];
      default: return valVector[7:0];
   endcase
endfunction

function Bit#(8) intra4x4SelectLeft( Bit#(40) valVector, Bit#(3) idx );
   case(idx)
      0: return valVector[15:8];
      1: return valVector[23:16];
      2: return valVector[31:24];
      3: return valVector[39:32];
      default: return valVector[7:0];
   endcase
endfunction

function Bit#(8) select32to8( Bit#(32) valVector, Bit#(2) idx );
   case(idx)
      0: return valVector[7:0];
      1: return valVector[15:8];
      2: return valVector[23:16];
      3: return valVector[31:24];
   endcase
endfunction

function Bit#(8) select16to8( Bit#(16) valVector, Bit#(1) idx );
   case(idx)
      0: return valVector[7:0];
      1: return valVector[15:8];
   endcase
endfunction

function Bool absDiffGEFour14( Bit#(14) val1, Bit#(14) val2 );
   Int#(15) int1 = unpack(signExtend(val1));
   Int#(15) int2 = unpack(signExtend(val2));
   if(int1>=int2)
      return (int1 >= (int2+4));
   else
      return (int2 >= (int1+4));
endfunction

function Bool absDiffGEFour12( Bit#(12) val1, Bit#(12) val2 );
   Int#(13) int1 = unpack(signExtend(val1));
   Int#(13) int2 = unpack(signExtend(val2));
   if(int1>=int2)
      return (int1 >= (int2+4));
   else
      return (int2 >= (int1+4));
endfunction


//-----------------------------------------------------------
// Prediction Module
//-----------------------------------------------------------


(* synthesize *)
module mkPrediction( IPrediction );

   //Common state
   FIFO#(EntropyDecOT)   infifo     <- mkSizedFIFO(prediction_infifo_size);
   FIFO#(InverseTransOT) infifo_ITB <- mkSizedFIFO(prediction_infifo_ITB_size);
   FIFO#(EntropyDecOT)   outfifo    <- mkFIFO;
   Reg#(Bool)            passFlag   <- mkReg(True);
   Reg#(Bit#(4))         blockNum   <- mkReg(0);
   Reg#(Bit#(4))         pixelNum   <- mkReg(0);

   Reg#(Bit#(PicWidthSz))  picWidth  <- mkReg(maxPicWidthInMB);
   Reg#(Bit#(PicHeightSz)) picHeight <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   firstMb   <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   currMb    <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   currMbHor <- mkReg(0);//horizontal position of currMb
   Reg#(Bit#(PicHeightSz)) currMbVer <- mkReg(0);//vertical position of currMb

   FIFOF#(OutState)   outstatefifo   <- mkFIFOF;        
   FIFOF#(NextOutput) nextoutputfifo <- mkFIFOF;
   Reg#(Bit#(4))   outBlockNum    <- mkReg(0);
   Reg#(Bit#(4))   outPixelNum    <- mkReg(0);
   FIFO#(Vector#(4,Bit#(8))) predictedfifo  <- mkSizedFIFO(prediction_predictedfifo_size);
   Reg#(Bit#(1))   outChromaFlag  <- mkReg(0);
   Reg#(Bool)      outFirstQPFlag <- mkReg(False);

   DoNotFire donotfire <- mkDoNotFire();
   
   //Reg#(Vector#(16,Bit#(8))) workVector       <- mkRegU();
   
   //Inter state
   Interpolator interpolator <- mkInterpolator();
   Reg#(InterState) interstate <- mkReg(Start);
   Reg#(Bit#(PicAreaSz)) interPskipCount <- mkReg(0);
   Reg#(Vector#(5,InterBlockMv)) interTopVal <- mkRegU();
   Reg#(Vector#(4,InterBlockMv)) interLeftVal <- mkRegU();
   Reg#(Vector#(4,InterBlockMv)) interTopLeftVal <- mkRegU();
   FIFO#(MemReq#(TAdd#(PicWidthSz,2),32)) interMemReqQ <- mkFIFO;
   Reg#(MemReq#(TAdd#(PicWidthSz,2),32)) interMemReqQdelay <- mkRegU();
   FIFO#(MemResp#(32))  interMemRespQ <- mkFIFO;
   Reg#(Bit#(3)) interReqCount <- mkReg(0);
   Reg#(Bit#(3)) interRespCount <- mkReg(0);

   Reg#(Bit#(2)) interStepCount <- mkReg(0);
   Reg#(Bit#(2)) interMbPartNum <- mkReg(0);
   Reg#(Bit#(2)) interSubMbPartNum <- mkReg(0);
   Reg#(Bit#(2)) interPassingCount <- mkReg(0);
   Reg#(Vector#(4,Bit#(4))) interRefIdxVector <- mkRegU();
   Reg#(Vector#(4,Bit#(2))) interSubMbTypeVector <- mkRegU();
   RFile1#(Bit#(4),Tuple2#(Bit#(14),Bit#(12))) interMvFile <- mkRFile1Full();
   Reg#(Bit#(15)) interMvDiffTemp <- mkReg(0);
   FIFO#(Tuple2#(Bit#(15),Bit#(13))) interMvDiff <- mkFIFO;
   Reg#(Bit#(5)) interNewestMv <- mkReg(0);

   // Registers for pipelining the interStage rule

   Reg#(Bit#(3)) partWidthR <- mkRegU();
   Reg#(Bit#(3)) partHeightR <- mkRegU();
   Reg#(Bit#(3)) numPartR <- mkRegU();
   Reg#(Bit#(3)) numSubPartR <- mkRegU();
   Reg#(Bit#(2)) subMbTypeR <- mkRegU();
   Reg#(Bool) calcmvR <- mkRegU();
   Reg#(Bool) leftmvR <- mkRegU();
   Reg#(Bit#(4)) refIndexR <- mkRegU();
   Reg#(Vector#(3,InterBlockMv)) blockABCR <- mkRegU();
   Reg#(Bit#(14)) mvhorfinalR <- mkRegU();
   Reg#(Bit#(12)) mvverfinalR <- mkRegU();
   Reg#(Bit#(5)) interNewestMvNextR <- mkRegU();

   
   Reg#(Bit#(2)) interIPStepCount <- mkReg(0);
   Reg#(Bit#(2)) interIPMbPartNum <- mkReg(0);
   Reg#(Bit#(2)) interIPSubMbPartNum <- mkReg(0);

   Reg#(Bit#(PicWidthSz)) interCurrMbDiff <- mkReg(0);

   Reg#(Vector#(4,Bool)) interTopNonZeroTransCoeff <- mkRegU();
   Reg#(Vector#(4,Bool)) interLeftNonZeroTransCoeff <- mkRegU();
   FIFO#(Tuple2#(Bit#(2),Bit#(2))) interBSfifo <- mkSizedFIFO(32);
   Reg#(Bool) interBSoutput <- mkReg(True);
   FIFO#(InterBlockMv) interOutBlockMvfifo <- mkSizedFIFO(8);
   
   
   //Intra state
   Reg#(IntraState)     intrastate      <- mkReg(Start);
   Reg#(Bit#(1))        intraChromaFlag <- mkReg(0);
   FIFO#(MemReq#(TAdd#(PicWidthSz,2),68)) intraMemReqQ  <- mkFIFO;
   Reg#(MemReq#(TAdd#(PicWidthSz,2),68)) intraMemReqQdelay <- mkRegU;
   FIFO#(MemResp#(68))  intraMemRespQ <- mkFIFO;
   Reg#(Vector#(4,Bit#(4))) intra4x4typeLeft <- mkRegU();//15=unavailable, 14=inter-MB, 13=intra-non-4x4
   Reg#(Vector#(4,Bit#(4))) intra4x4typeTop  <- mkRegU();//15=unavailable, 14=inter-MB, 13=intra-non-4x4
   Reg#(Bit#(1)) ppsconstrained_intra_pred_flag <- mkReg(0);
   Reg#(Vector#(4,Bit#(40))) intraLeftVal <- mkRegU();
   Reg#(Vector#(9,Bit#(8))) intraLeftValChroma0 <- mkRegU();
   Reg#(Vector#(9,Bit#(8))) intraLeftValChroma1 <- mkRegU();
   Reg#(Vector#(5,Bit#(32))) intraTopVal <- mkRegU();
   Reg#(Vector#(4,Bit#(16))) intraTopValChroma0 <- mkRegU();
   Reg#(Vector#(4,Bit#(16))) intraTopValChroma1 <- mkRegU();
   Reg#(Bit#(32)) intraLeftValNext <- mkReg(0);
   Reg#(Bit#(2)) intra16x16_pred_mode <- mkReg(0);
   FIFO#(Bit#(4)) rem_intra4x4_pred_mode <- mkSizedFIFO(16);
   FIFO#(Bit#(2)) intra_chroma_pred_mode <- mkFIFO;
   Reg#(Bit#(4)) cur_intra4x4_pred_mode <- mkReg(0);
   Reg#(Bit#(1)) intraChromaTopAvailable <- mkReg(0);
   Reg#(Bit#(1)) intraChromaLeftAvailable <- mkReg(0);

   Reg#(Bit#(3)) intraReqCount <- mkReg(0);
   Reg#(Bit#(3)) intraRespCount <- mkReg(0);
   Reg#(Bit#(4)) intraStepCount <- mkReg(0);
   Reg#(Bit#(13)) intraSumA <-  mkReg(0);
   Reg#(Bit#(15)) intraSumB <-  mkReg(0);
   Reg#(Bit#(15)) intraSumC <-  mkReg(0);
   
   Reg#(Vector#(4,Bit#(8))) intraPredVector <- mkRegU();   

   //-----------------------------------------------------------
   // Rules

   //////////////////////////////////////////////////////////////////////////////
//   rule stateMonitor ( True );
//      if(predictedfifo.notEmpty())
//	 $display( "TRACE Prediction: stateMonitor predictedfifo.first() %0d", predictedfifo.first());////////////////////
//      if(infifo.first() matches tagged ITBresidual .xdata)
//	 $display( "TRACE Prediction: stateMonitor infifo.first() %0d", xdata);////////////////////
//      if(infifo.first() matches tagged ITBresidual .xdata)
//	 $display( "TRACE Prediction: stateMonitor outBlockNum outPixelNum outChromaFlag %0d %0d", outBlockNum, outPixelNum, outChromaFlag);////////////////////
//   endrule
   //////////////////////////////////////////////////////////////////////////////

   rule checkFIFO ( True );
      $display( "Trace Prediction: checkFIFO %h", infifo.first() );
   endrule
   rule checkFIFO_ITB ( True );
      $display( "Trace Prediction: checkFIFO_ITB %h", infifo_ITB.first() );
   endrule
   rule checkFIFO_predicted ( True );
      $display( "Trace Prediction: checkFIFO_predicted %h", predictedfifo.first() );
   endrule

   
   rule passing ( passFlag && !outstatefifo.notEmpty() && currMbHor<zeroExtend(picWidth) );
      $display( "Trace Prediction: passing infifo packed %h", pack(infifo.first()));
      case (infifo.first()) matches
	 tagged NewUnit . xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	       $display("ccl4newunit");
	       $display("ccl4rbspbyte %h", xdata);
	    end
	 tagged SPSpic_width_in_mbs .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	       picWidth <= xdata;
	       interpolator.setPicWidth(xdata);
	    end
	 tagged SPSpic_height_in_map_units .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	       picHeight <= xdata;
	       interpolator.setPicHeight(xdata);
	    end
	 tagged PPSconstrained_intra_pred_flag .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       ppsconstrained_intra_pred_flag <= xdata;
	    end
	 tagged SHfirst_mb_in_slice .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	       firstMb   <= xdata;
	       currMb    <= xdata;
	       currMbHor <= xdata;
	       currMbVer <= 0;
	       intra4x4typeLeft <= replicate(15);
	       interTopLeftVal <= replicate(tagged NotInter 0);
	       if(xdata==0)
		  interLeftVal <= replicate(tagged NotInter 0);
	       outFirstQPFlag <= True;
	    end
	 tagged SDmb_skip_run .xdata : passFlag <= False;
	 tagged SDMmbtype .xdata : passFlag <= False;
	 tagged EndOfFile :
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	       $display( "INFO Prediction: EndOfFile reached" );
	       //$finish(0);////////////////////////////////
	    end
	 default:
	    begin
	       infifo.deq();
	       outfifo.enq(infifo.first());
	    end
      endcase
   endrule


   rule inputing ( !passFlag );
      $display( "Trace Prediction: inputing infifo packed %h", pack(infifo.first()));
      case (infifo.first()) matches
	 tagged SDmb_skip_run .xdata :
	    begin
	       if(interstate==Start && intrastate==Start)
		  begin
		     if(interPskipCount < xdata)
			begin
			   if(!outstatefifo.notEmpty() || interCurrMbDiff<picWidth-1)
			      begin
				 $display( "Trace Prediction: passing SDmb_skip_run %0d", xdata);
				 outstatefifo.enq(Inter);
				 interstate <= InterPskip;
				 interReqCount <= 1;
				 interRespCount <= 1;
				 intra4x4typeLeft <= replicate(14);
				 intra4x4typeTop <= replicate(14);
				 interTopLeftVal <= update(interTopLeftVal , 0, (tagged NotInter 0));
				 interTopVal <= replicate(tagged NotInter 0);
				 interPskipCount <= interPskipCount+1;
				 interNewestMv <= 0;
				 interRefIdxVector <= replicate(0);
				 interCurrMbDiff <= interCurrMbDiff+1;
				 nextoutputfifo.enq(SkipMB);
			      end
			   else
			      donotfire.doNotFire();
			end
		     else
			begin
			   $display( "Trace Prediction: passing no SDmb_skip_run");
			   interPskipCount <= 0;
			   infifo.deq();
			end
		  end
	       else
		  donotfire.doNotFire();
	    end
	 tagged SDMmbtype .xdata :
	    begin
	       if(interstate==Start && intrastate==Start)//not necessary (just need to keep inter from feeding predictedfifo or change intra state until intrastate==Start)
		  begin
		     infifo.deq();
		     $display( "INFO Prediction: SDMmbtype %0d", xdata);
		     if(mbPartPredMode(xdata,0)==Intra_16x16)
			begin
			   if(!outstatefifo.notEmpty())
			      begin
				 outstatefifo.enq(Intra);
				 intrastate <= Intra16x16;
				 if(xdata matches tagged I_16x16 {intra16x16PredMode:.tempv1, codedBlockPatternChroma:.tempv2, codedBlockPatternLuma:.tempv3})
				    intra16x16_pred_mode <= tempv1;
				 else
				    $display( "ERROR Prediction: MacroblockLayer 5 sdmmbtype not I_16x16" );
				 intraReqCount <= 1;
				 intraRespCount <= 1;
				 interTopLeftVal <= replicate(tagged NotInter 1);
				 interLeftVal <= replicate(tagged NotInter 1);
				 interTopVal <= replicate(tagged NotInter 1);
			      end
			   else
			      donotfire.doNotFire();
			end
		     else if(xdata==I_NxN)
			begin
			   if(!outstatefifo.notEmpty())
			      begin
				 outstatefifo.enq(Intra4x4);
				 intrastate <= Intra4x4;
				 intraReqCount <= 1;
				 intraRespCount <= 1;
				 interTopLeftVal <= replicate(tagged NotInter 1);
				 interLeftVal <= replicate(tagged NotInter 1);
				 interTopVal <= replicate(tagged NotInter 1);
			      end
			   else
			      donotfire.doNotFire();
			end
		     else if(xdata==I_PCM)
			begin
			   $display( "ERROR Prediction: I_PCM not implemented yet");
			   $finish;////////////////////////////////////////////////////////////////////////////////////////
			   intra4x4typeLeft <= replicate(13);
			   intra4x4typeTop <= replicate(13);
			   interTopLeftVal <= replicate(tagged NotInter 1);
			   interLeftVal <= replicate(tagged NotInter 1);
			   interTopVal <= replicate(tagged NotInter 1);
			end
		     else
			begin
			   if(!outstatefifo.notEmpty() || interCurrMbDiff<picWidth-1)
			      begin
				 outstatefifo.enq(Inter);
				 case(xdata)
				    P_L0_16x16: interstate <= InterP16x16;
				    P_L0_L0_16x8: interstate <= InterP16x8;
				    P_L0_L0_8x16: interstate <= InterP8x16;
				    P_8x8: interstate <= InterP8x8;
				    P_8x8ref0: interstate <= InterP8x8ref0;
				    default: $display( "ERROR Prediction: passing SDMmbtype inter prediction unknown mbtype");
				 endcase
				 interReqCount <= 1;
				 interRespCount <= 1;
				 intra4x4typeLeft <= replicate(14);/////////////////////////////////////////////////////////////////////////////
				 intra4x4typeTop <= replicate(14);
				 interTopLeftVal <= update(interTopLeftVal , 0, (tagged NotInter 0));
				 interTopVal <= replicate(tagged NotInter 0);
				 interNewestMv <= 0;
				 interRefIdxVector <= replicate(0);
				 nextoutputfifo.enq(NonSkipMB);
			      end
			   else
			      donotfire.doNotFire();
			end
		     interCurrMbDiff <= interCurrMbDiff+1;
		  end
	       else
		  donotfire.doNotFire();
	    end
	 tagged SDMMrem_intra4x4_pred_mode .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       rem_intra4x4_pred_mode.enq(xdata);
	    end
	 tagged SDMMintra_chroma_pred_mode .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       intra_chroma_pred_mode.enq(xdata);
	    end
	 tagged SDMMref_idx_l0 .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       interRefIdxVector <= update(interRefIdxVector,interPassingCount,xdata[3:0]);
	       if(interstate==InterP16x16 || interPassingCount==1)
		  interPassingCount <= 0;
	       else
		  interPassingCount <= interPassingCount+1;
	    end
	 tagged SDMMmvd_l0 .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       if(interPassingCount==1)
		  begin
		     Bit#(13) interMvDiffTemp2 = truncate(xdata);
		     interMvDiff.enq(tuple2(interMvDiffTemp,interMvDiffTemp2));
		     interPassingCount <= 0;
		  end
	       else
		  begin
		     interMvDiffTemp <= truncate(xdata);
		     interPassingCount <= interPassingCount+1;
		  end
	    end
	 tagged SDMSsub_mb_type .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       interSubMbTypeVector <= update(interSubMbTypeVector,interPassingCount,xdata);
	       interPassingCount <= interPassingCount+1;
	    end
	 tagged SDMSref_idx_l0 .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       interRefIdxVector <= update(interRefIdxVector,interPassingCount,xdata[3:0]);
	       interPassingCount <= interPassingCount+1;
	    end
	 tagged SDMSmvd_l0 .xdata :
	    begin
	       infifo.deq();
	       ////outfifo.enq(infifo.first());
	       if(interPassingCount==1)
		  begin
		     Bit#(13) interMvDiffTemp2 = truncate(xdata);
		     interMvDiff.enq(tuple2(interMvDiffTemp,interMvDiffTemp2));
		     interPassingCount <= 0;
		  end
	       else
		  begin
		     interMvDiffTemp <= truncate(xdata);
		     interPassingCount <= interPassingCount+1;
		  end
	    end
	 default: passFlag <= True;
      endcase
   endrule

   
   rule outputing ( currMbHor<zeroExtend(picWidth) );
      Bit#(1) outputFlag = 0;
      Vector#(4,Bit#(8)) outputVector = replicate(0);
      Bit#(2) blockHor = {outBlockNum[2],outBlockNum[0]};
      Bit#(2) blockVer = {outBlockNum[3],outBlockNum[1]};
      Bit#(2) pixelVer = {outPixelNum[3],outPixelNum[2]};
      Bit#(4) totalVer = {blockVer,pixelVer};
      //$display( "Trace Prediction: outputing" );
      if(outFirstQPFlag)
	 begin
	    if(infifo_ITB.first() matches tagged IBTmb_qp .xdata)
	       begin
		  infifo_ITB.deq();
		  outfifo.enq(IBTmb_qp {qpy:xdata.qpy,qpc:xdata.qpc});
		  outFirstQPFlag <= False;
		  $display( "Trace Prediction: outputing outFirstQP %h %h %h", outBlockNum, outPixelNum, xdata);
	       end
	    else
	       $display( "ERROR Prediction: outputing unexpected infifo_ITB.first()");
	 end
      else if(nextoutputfifo.first() == SkipMB)
	 begin
	    if(interBSoutput && outChromaFlag==0 && outPixelNum==0)
	       begin
		  interBSoutput <= False;
		  interBSfifo.deq();
		  Bit#(2) tempHorBS = tpl_1(interBSfifo.first());
		  Bit#(2) tempVerBS = tpl_2(interBSfifo.first());
		  Bit#(3) horBS = (tempHorBS==3 ? 4 : (interLeftNonZeroTransCoeff[blockVer] ? 2 : zeroExtend(tempHorBS)));
		  Bit#(3) verBS = (tempVerBS==3 ? 4 : (interTopNonZeroTransCoeff[blockHor]&&blockVer!=0 ? 2 : zeroExtend(tempVerBS)));
		  outfifo.enq(PBbS {bShor:horBS,bSver:verBS});
		  interLeftNonZeroTransCoeff <= update(interLeftNonZeroTransCoeff, blockVer, False);
		  interTopNonZeroTransCoeff <= update(interTopNonZeroTransCoeff, blockHor, False);
		  $display( "Trace Prediction: outputing SkipMB bS %h %h %h %h", outBlockNum, outPixelNum, currMbHor, currMbVer);
	       end
	    else
	       begin
		  interBSoutput <= True;
		  outputVector = predictedfifo.first();
		  outfifo.enq(tagged PBoutput outputVector);
		  outputFlag = 1;
		  predictedfifo.deq();
		  $display( "Trace Prediction: outputing SkipMB out %h %h %h", outBlockNum, outPixelNum, outputVector);
	       end
	 end
      else
	 begin
	    case ( infifo_ITB.first() ) matches
	       tagged IBTmb_qp .xdata :
		  begin
		     infifo_ITB.deq();
		     outfifo.enq(tagged IBTmb_qp {qpy:xdata.qpy,qpc:xdata.qpc});
		     outFirstQPFlag <= False;
		     $display( "Trace Prediction: outputing ITBmb_qp %h %h %h", outBlockNum, outPixelNum, xdata);
		  end
	       tagged ITBresidual .xdata :
		  begin
		     if(interBSoutput && outChromaFlag==0 && outPixelNum==0)
			begin
			   interBSoutput <= False;
			   if(outstatefifo.first() != Inter)
			      outfifo.enq(tagged PBbS {bShor:(blockHor==0 ? 4 : 3),bSver:(blockVer==0 ? 4 : 3)});
			   else
			      begin
				 interBSfifo.deq();
				 Bit#(2) tempHorBS = tpl_1(interBSfifo.first());
				 Bit#(2) tempVerBS = tpl_2(interBSfifo.first());
				 Bit#(3) horBS = (tempHorBS==3 ? 4 : 2);
				 Bit#(3) verBS = (tempVerBS==3 ? 4 : 2);
				 outfifo.enq(tagged PBbS {bShor:horBS,bSver:verBS});
			      end
			   interLeftNonZeroTransCoeff <= update(interLeftNonZeroTransCoeff, blockVer, True);
			   interTopNonZeroTransCoeff <= update(interTopNonZeroTransCoeff, blockHor, True);
			   $display( "Trace Prediction: outputing ITBresidual bS %h %h %h %h %h", outChromaFlag, outBlockNum, outPixelNum, currMbHor, currMbVer);
			end
		     else
			begin
			   interBSoutput <= True;
			   Bit#(11) tempOutputValue = 0;
			   for(Integer ii=0; ii<4; ii=ii+1)
			      begin
				 tempOutputValue = signExtend(xdata[ii]) + zeroExtend((predictedfifo.first())[ii]);
				 if(tempOutputValue[10]==1)
				    outputVector[ii] = 0;
				 else if(tempOutputValue[9:0] > 255)
				    outputVector[ii] = 255;
				 else
				    outputVector[ii] = tempOutputValue[7:0];
			      end
			   outfifo.enq(tagged PBoutput outputVector);
			   infifo_ITB.deq();
			   predictedfifo.deq();
			   outputFlag = 1;
			   $display( "Trace Prediction: outputing ITBresidual out %h %h %h %h %h %h", outChromaFlag, outBlockNum, outPixelNum, predictedfifo.first(), xdata, outputVector);
			end
		  end
	       tagged ITBcoeffLevelZeros :
		  begin
		     if(interBSoutput && outChromaFlag==0 && outPixelNum==0)
			begin
			   interBSoutput <= False;
			   if(outstatefifo.first() != Inter)
			      outfifo.enq(tagged PBbS {bShor:(blockHor==0 ? 4 : 3),bSver:(blockVer==0 ? 4 : 3)});
			   else
			      begin
				 interBSfifo.deq();
				 Bit#(2) tempHorBS = tpl_1(interBSfifo.first());
				 Bit#(2) tempVerBS = tpl_2(interBSfifo.first());
				 Bit#(3) horBS = (tempHorBS==3 ? 4 : (interLeftNonZeroTransCoeff[blockVer] ? 2 : zeroExtend(tempHorBS)));
				 Bit#(3) verBS = (tempVerBS==3 ? 4 : (interTopNonZeroTransCoeff[blockHor]&&blockVer!=0 ? 2 : zeroExtend(tempVerBS)));
				 outfifo.enq(tagged PBbS {bShor:horBS,bSver:verBS});
			      end
			   interLeftNonZeroTransCoeff <= update(interLeftNonZeroTransCoeff, blockVer, False);
			   interTopNonZeroTransCoeff <= update(interTopNonZeroTransCoeff, blockHor, False);
			   $display( "Trace Prediction: outputing ITBcoeffLevelZeros bS %h %h %h %h %h", outChromaFlag, outBlockNum, outPixelNum, currMbHor, currMbVer);
			end
		     else
			begin
			   interBSoutput <= True;
			   if(outPixelNum == 12)
			      infifo_ITB.deq();
			   outputVector = predictedfifo.first();
			   outfifo.enq(tagged PBoutput outputVector);
			   outputFlag = 1;
			   predictedfifo.deq();
			   $display( "Trace Prediction: outputing ITBcoeffLevelZeros out %h %h %h %h %h", outChromaFlag, outBlockNum, outPixelNum, predictedfifo.first(), outputVector);
			end
		  end
	       default: $display( "ERROR Prediction: outputing unknown infifo_ITB input" );
	    endcase
	 end
 
      if(outputFlag == 1)
	 begin
	    $display("ccl4PBoutput %0d", outputVector[0]);
	    $display("ccl4PBoutput %0d", outputVector[1]);
	    $display("ccl4PBoutput %0d", outputVector[2]);
	    $display("ccl4PBoutput %0d", outputVector[3]);

	    if(outBlockNum==0 && pixelVer==0 && outChromaFlag==0 && currMb!=firstMb && picWidth>1)
	       begin
		  intraMemReqQ.enq(intraMemReqQdelay);
		  interMemReqQ.enq(interMemReqQdelay);
		  //$display( "TRACE Prediction: passing storing addr data");//////////////////
	       end
	    
	    if(blockHor==3 || (blockHor[0]==1 && outChromaFlag==1) || (outstatefifo.first()==Intra4x4 && outChromaFlag==0))
	       begin
		  if(outChromaFlag==0)
		     begin
			Bit#(32) intraLeftValNextTemp = intraLeftValNext;
			if(totalVer==0 || (outstatefifo.first()==Intra4x4 && pixelVer==0))
			   begin
			      Bit#(32) tempValSet = select(intraTopVal,blockHor);
			      intraLeftValNextTemp = zeroExtend(tempValSet[31:24]);
			   end
			case(pixelVer)
			   0:intraLeftValNext <= {intraLeftValNextTemp[31:16],outputVector[3],intraLeftValNextTemp[7:0]};
			   1:intraLeftValNext <= {intraLeftValNextTemp[31:24],outputVector[3],intraLeftValNextTemp[15:0]};
			   2:intraLeftValNext <= {outputVector[3],intraLeftValNextTemp[23:0]};
			   3:
			   begin
			      intraLeftVal <= update(intraLeftVal,blockVer,{outputVector[3],intraLeftValNextTemp});
			      intraLeftValNext <= zeroExtend(outputVector[3]);
			      if(outstatefifo.first()==Intra4x4)
				 intra4x4typeLeft <= update(intra4x4typeLeft,blockVer,cur_intra4x4_pred_mode);
			      else if(outstatefifo.first()==Intra)
				 intra4x4typeLeft <= update(intra4x4typeLeft,blockVer,13);
			      else
				 intra4x4typeLeft <= update(intra4x4typeLeft,blockVer,14);
			   end
			endcase
		     end
		  else
		     begin
			if(outBlockNum[2]==0)
			   intraLeftValChroma0 <= update(intraLeftValChroma0,totalVer+1,outputVector[3]);
			else
			   intraLeftValChroma1 <= update(intraLeftValChroma1,totalVer+1,outputVector[3]);
		     end
	       end
			   
	    if(pixelVer==3 && (blockVer==3 || (blockVer[0]==1 && outChromaFlag==1) || (outstatefifo.first()==Intra4x4 && outChromaFlag==0)))
	       begin
		  if(outChromaFlag==0)
		     begin
			intraTopVal <= update(intraTopVal,blockHor,{outputVector[3],outputVector[2],outputVector[1],outputVector[0]});
			if(outstatefifo.first()==Intra4x4)
			   intra4x4typeTop <= update(intra4x4typeTop,blockHor,cur_intra4x4_pred_mode);
			else if(outstatefifo.first()==Intra)
			   intra4x4typeTop <= update(intra4x4typeTop,blockHor,13);
			else
			   intra4x4typeTop <= update(intra4x4typeTop,blockHor,14);
		     end
		  else
		     begin
			if(outBlockNum[2]==0)
			   begin
			      Vector#(4,Bit#(16)) intraTopValChroma0Next = intraTopValChroma0;
			      intraTopValChroma0Next[{blockHor[0],1'b0}] = {outputVector[1],outputVector[0]};
			      intraTopValChroma0Next[{blockHor[0],1'b1}] = {outputVector[3],outputVector[2]};
			      intraTopValChroma0 <= intraTopValChroma0Next;
			   end
			else
			   begin
			      Vector#(4,Bit#(16)) intraTopValChroma1Next = intraTopValChroma1;
			      intraTopValChroma1Next[{blockHor[0],1'b0}] = {outputVector[1],outputVector[0]};
			      intraTopValChroma1Next[{blockHor[0],1'b1}] = {outputVector[3],outputVector[2]};
			      intraTopValChroma1 <= intraTopValChroma1Next;
			   end
		     end
	       end

	    if(outChromaFlag==1 && outBlockNum==7)
	       begin
		  Bit#(PicWidthSz) tempStoreAddr = truncate(currMbHor);
		  InterBlockMv outBlockMv = interOutBlockMvfifo.first();
		  if(outBlockMv matches tagged BlockMv .bdata)
		     begin
			outBlockMv = (BlockMv {refIdx:bdata.refIdx,mvhor:bdata.mvhor,mvver:bdata.mvver,nonZeroTransCoeff:(interTopNonZeroTransCoeff[pixelVer]?1:0)});
			interOutBlockMvfifo.deq();
		     end
		  else if(pixelVer==3)
		     interOutBlockMvfifo.deq();
		  if(pixelVer==3 && picWidth>1)
		     interMemReqQdelay <= StoreReq {addr:{tempStoreAddr,pixelVer},data:pack(outBlockMv)};
		  else
		     interMemReqQ.enq(tagged StoreReq {addr:{tempStoreAddr,pixelVer},data:pack(outBlockMv)});
		  if(pixelVer>0)
		     begin
			Bit#(4)  intra4x4typeTopStore = ((outstatefifo.first()==Inter) ? 14 : ((outstatefifo.first()!=Intra4x4) ? 13: intra4x4typeTop[(pixelVer-1)]));
			Bit#(32) intraTopValStore = intraTopVal[(pixelVer-1)];
			Bit#(16) intraTopValChroma0Store = intraTopValChroma0[(pixelVer-1)];
			Bit#(16) intraTopValChroma1Store = (pixelVer<3 ? intraTopValChroma1[(pixelVer-1)] : {outputVector[1],outputVector[0]});
			Bit#(68) intraStore = {intra4x4typeTopStore,intraTopValChroma1Store,intraTopValChroma0Store,intraTopValStore};
			intraMemReqQ.enq(tagged StoreReq {addr:{tempStoreAddr,(pixelVer-1)},data:intraStore});
			if(pixelVer==3)
			   begin
			      intra4x4typeTopStore = ((outstatefifo.first()==Inter) ? 14 : ((outstatefifo.first()!=Intra4x4) ? 13: intra4x4typeTop[3]));
			      intraTopValStore = intraTopVal[3];
			      intraTopValChroma0Store = intraTopValChroma0[3];
			      intraTopValChroma1Store = {outputVector[3],outputVector[2]};
			      intraStore = {intra4x4typeTopStore,intraTopValChroma1Store,intraTopValChroma0Store,intraTopValStore};
			      intraMemReqQdelay <= StoreReq {addr:{tempStoreAddr,2'b11},data:intraStore};
			   end
		     end
	       end
	    outPixelNum <= outPixelNum+4;
	    if(outPixelNum == 12)
	       begin
		  if(outChromaFlag==0)
		     begin
			outBlockNum <= outBlockNum+1;
			if(outBlockNum == 15)
			   outChromaFlag <= 1;
			if(nextoutputfifo.first() == Intra4x4)
			   nextoutputfifo.deq();
		     end
		  else
		     begin
			if(outBlockNum == 7)
			   begin
			      outBlockNum <= 0;
			      outChromaFlag <= 0;
			      currMb <= currMb+1;
			      currMbHor <= currMbHor+1;
			      interCurrMbDiff <= interCurrMbDiff-1;
			      outstatefifo.deq;
			      intrastate <= Start;
			      if(truncate(currMbHor)==picWidth-1 && currMbVer==picHeight-1)
				 interpolator.endOfFrame();
			      nextoutputfifo.deq();
			   end
			else
			   outBlockNum <= outBlockNum+1;
		     end
	       end
	 end
   endrule


   rule currMbHorUpdate( !(currMbHor<zeroExtend(picWidth)) );
      Bit#(PicAreaSz) temp = zeroExtend(picWidth);
      if((currMbHor >> 3) >= temp)
	 begin
	    currMbHor <= currMbHor - (temp << 3);
	    currMbVer <= currMbVer + 8;
	 end
      else
	 begin
	    currMbHor <= currMbHor - temp;
	    currMbVer <= currMbVer + 1;
	 end
      //$display( "Trace Prediction: currMbHorUpdate %h %h", currMbHor, currMbVer);
   endrule


   // inter prediction rules

   rule interSendReq ( interReqCount>0 && currMbHor<zeroExtend(picWidth) );
      Bit#(PicAreaSz) currMbHorTemp = currMbHor+zeroExtend(interCurrMbDiff)-1;
      Bit#(PicAreaSz) currMbTemp = currMb+zeroExtend(interCurrMbDiff)-1;
      if( currMbHorTemp >= zeroExtend(picWidth) )
	 currMbHorTemp = currMbHorTemp-zeroExtend(picWidth);
      Bit#(PicWidthSz) temp2 = truncate(currMbHorTemp);
      Bit#(TAdd#(PicWidthSz,2)) temp = 0;
      Bool noMoreReq = False;
      if( currMbTemp < zeroExtend(picWidth) )
	 noMoreReq = True;
      else
	 begin
	    if(interReqCount<5)
	       begin
		  Bit#(2) temp3 = truncate(interReqCount-1);
		  temp = {temp2,temp3};
	       end
	    else if(interReqCount==5)
	       begin
		  if((currMbHorTemp+1)<zeroExtend(picWidth))
		     temp = {(temp2+1),2'b00};
		  else if(currMbHorTemp>0 && currMbTemp-firstMb>zeroExtend(picWidth))
		     temp = {(temp2-1),2'b11};
		  else
		     noMoreReq = True;
	       end
	    else if(interReqCount==6)
	       begin
		  if((currMbHorTemp+1)<zeroExtend(picWidth) && currMbHorTemp>0 && currMbTemp-firstMb>zeroExtend(picWidth))
		     temp = {(temp2-1),2'b11};
		  else
		     noMoreReq = True;
	       end
	    else
	       noMoreReq = True;
	 end
      if(!noMoreReq)
	 begin
      	    interMemReqQ.enq(tagged LoadReq temp);
	    interReqCount <= interReqCount+1;
	    //$display( "TRACE Prediction: interSendReq addr %0d",temp);///////////////////////
	 end
      else
	 interReqCount <= 0;
      $display( "Trace Prediction: interSendReq %h %h %h", interstate, interReqCount, temp);
   endrule


   rule interReceiveNoResp ( interRespCount>0 && currMbHor<zeroExtend(picWidth) && currMb+zeroExtend(interCurrMbDiff)-1<zeroExtend(picWidth) );
      Bit#(PicAreaSz) currMbHorTemp = currMbHor+zeroExtend(interCurrMbDiff)-1;
      if( currMbHorTemp >= zeroExtend(picWidth) )
	 currMbHorTemp = currMbHorTemp-zeroExtend(picWidth);
      interRespCount <= 0;
      interStepCount <= 1;
      interIPStepCount <= 1;
      if(currMbHorTemp == 0)
	 begin
	    interLeftVal <= replicate(tagged NotInter 0);
	    interTopLeftVal <= replicate(tagged NotInter 0);
	 end
      $display( "Trace Prediction: interReceiveNoResp %h %h", interstate, interRespCount);
   endrule

   
   rule interReceiveResp ( interRespCount>0 && interRespCount<7 && currMbHor<zeroExtend(picWidth) &&& interMemRespQ.first() matches tagged LoadResp .data);
      Bit#(PicAreaSz) currMbHorTemp = currMbHor+zeroExtend(interCurrMbDiff)-1;
      Bit#(PicAreaSz) currMbTemp = currMb+zeroExtend(interCurrMbDiff)-1;
      if( currMbHorTemp >= zeroExtend(picWidth) )
	 currMbHorTemp = currMbHorTemp-zeroExtend(picWidth);
      Bool noMoreResp = False;
      Bit#(2) temp2bit = 0;
      InterBlockMv unpackedData = unpack(data);
      Vector#(5,InterBlockMv) interTopValNext = interTopVal;
      Vector#(4,InterBlockMv) interTopLeftValNext = interTopLeftVal;
      if(interRespCount<5)
	 begin
	    temp2bit = truncate(interRespCount-1);
	    interTopValNext[temp2bit] = unpackedData;
	    if((interRespCount==4 || (interRespCount==1 && (interstate==InterPskip || interstate==InterP16x16 || interstate==InterP16x8))) 
	       && (!((currMbHorTemp+1)<zeroExtend(picWidth)) && !(currMbHorTemp>0 && currMbTemp-firstMb>zeroExtend(picWidth))))
	       noMoreResp = True;
	 end
      else if(interRespCount==5)
	 begin
	    if((currMbHorTemp+1)<zeroExtend(picWidth))
	       begin
		  interTopValNext[4] = unpackedData;
		  if(!(currMbHorTemp>0 && currMbTemp-firstMb>zeroExtend(picWidth)))
		     noMoreResp = True;
	       end
	    else
	       begin
		  interTopLeftValNext[0] = unpackedData;
		  noMoreResp = True;
	       end
	 end
      else
	 begin
	    interTopLeftValNext[0] = unpackedData;
	    noMoreResp = True;
	 end
      interMemRespQ.deq();
      //$display( "TRACE Prediction: interReceiveResp data %h",data);///////////////////////
      if(!noMoreResp)
	 interRespCount <= interRespCount+1;
      else
	 begin
	    interRespCount <= 0;
	    interStepCount <= 1;
	    interIPStepCount <= 1;
	    if(currMbHorTemp == 0)
	       begin
		  interLeftVal <= replicate(tagged NotInter 0);
		  interTopLeftValNext = replicate(tagged NotInter 0);
	       end
	 end
      interTopVal <= interTopValNext;
      interTopLeftVal <= interTopLeftValNext;
      $display( "Trace Prediction: interReceiveResp %h %h %h", interstate, interRespCount, data);
   endrule


   rule interProcessStep ( interStepCount>0 && currMbHor<zeroExtend(picWidth) );
      Bit#(PicAreaSz) currMbTemp = currMb+zeroExtend(interCurrMbDiff)-1;
      Bit#(2) blockHor = {interMbPartNum[0],interSubMbPartNum[0]};
      Bit#(2) blockVer = {interMbPartNum[1],interSubMbPartNum[1]};

      if(interStepCount == 1)
         begin
           Bit#(3) partWidth = 0;
           Bit#(3) partHeight = 0;
           Bit#(3) numPart = 1;
           Bit#(3) numSubPart = 1;
           Bit#(2) subMbType = 0;
           Bool noBlockC = False;
           Bool calcmv = False;
           Bool leftmv = False;
           if(interstate==InterPskip || interstate==InterP16x16)
	      begin
	         partWidth = 4;
	         partHeight = 4;
	         numPart = 1;
	         calcmv = (interMbPartNum==0 && interSubMbPartNum==0);
	         leftmv = (blockHor>0);
	      end
           else if(interstate==InterP16x8)
	      begin
	         partWidth = 4;
                 partHeight = 2;
	         numPart = 2;
	         if(interMbPartNum==2)
	            noBlockC = True;
	         calcmv = (interMbPartNum[0]==0 && interSubMbPartNum==0);
	         leftmv = (blockHor>0);
	      end
           else if(interstate==InterP8x16)
	      begin
	         partWidth = 2;
	         partHeight = 4;
	         numPart = 2;
	         calcmv = (interMbPartNum[1]==0 && interSubMbPartNum==0);
	         leftmv = !(blockVer>0);
	      end
           else if(interstate==InterP8x8 || interstate==InterP8x8ref0)
	      begin
	         numPart = 4;
	         subMbType = interSubMbTypeVector[interMbPartNum];
	         numSubPart = numSubMbPart(subMbType);
	         case(subMbType)
	            0:
	            begin
	               partWidth = 2;
		       partHeight = 2;
		       if(interMbPartNum==3)
		          noBlockC = True;
                       calcmv = (interSubMbPartNum==0);
		       leftmv = (blockHor[0]>0);
	            end
	            1:
	            begin
		       partWidth = 2;
		       partHeight = 1;
		       if(interSubMbPartNum==2)
		          noBlockC = True;
		       calcmv = (interSubMbPartNum[0]==0);
		       leftmv = True;
	            end
	            2: 
	            begin
		       partWidth = 1;
		       partHeight = 2;
		       calcmv = (interSubMbPartNum[1]==0);
		       leftmv = False;
	            end
	            3:
	            begin
		      partWidth = 1;
		      partHeight = 1;
		      if(interSubMbPartNum==3)
		         noBlockC = True;
		      calcmv = True;
	            end
	         endcase
	     end
          else
	    $display( "ERROR Prediction: interProcessStep unexpected interstate");

          Bit#(4) refIndex = ((interstate==InterPskip||interstate==InterP8x8ref0) ? 0 : interRefIdxVector[interMbPartNum]);
          Vector#(3,InterBlockMv) blockABC = replicate(tagged NotInter 0);
          if( currMbTemp-firstMb==0 && blockHor==0 )
	     blockABC[0] = (tagged NotInter 0);
          else
	     blockABC[0] = interLeftVal[blockVer];
          if( currMbTemp-firstMb<zeroExtend(picWidth) && blockVer==0 )
	     blockABC[1] = (tagged NotInter 0);
          else
	     blockABC[1] = interTopVal[blockHor];
          blockABC[2] = interTopVal[{1'b0,blockHor}+partWidth];
          if(noBlockC || blockABC[2]==(tagged NotInter 0))
	     blockABC[2] = interTopLeftVal[blockVer];
	  partWidthR <= partWidth;
	  partHeightR <= partHeight;
	  numPartR <= numPart;
	  numSubPartR <= numSubPart;
	  subMbTypeR <= subMbType;
	  calcmvR <= calcmv;
	  leftmvR <= leftmv;
	  refIndexR <= refIndex;
	  blockABCR <= blockABC;
	  interStepCount <= 2;
      end
   else if(interStepCount==2)
      begin
         Bit#(3) partWidth = partWidthR;
         Bit#(3) partHeight = partHeightR;
         Bit#(3) numPart = numPartR;
         Bit#(3) numSubPart = numSubPartR;
         Bit#(2) subMbType = subMbTypeR;
         Bool calcmv = calcmvR;
         Bool leftmv = leftmvR;
         Bit#(4) refIndex = refIndexR;
         Vector#(3,InterBlockMv) blockABC = blockABCR;
         Bit#(14) mvhorfinal = 0;
         Bit#(12) mvverfinal = 0;
         Bit#(5) interNewestMvNext = 0;
         if(calcmv)//motion vector caculation
	    begin
	       Vector#(3,Int#(14)) mvhorABC = replicate(0);
               Vector#(3,Int#(12)) mvverABC = replicate(0);
               Bit#(2) validCount = 0;
               Bit#(14) mvhorPred = 0;
               Bit#(12) mvverPred = 0;
               for(Integer ii=0; ii<3; ii=ii+1)
                  begin
		     if(blockABC[ii] matches tagged BlockMv .xdata)
		        begin
			   mvhorABC[ii] = unpack(xdata.mvhor);
			   mvverABC[ii] = unpack(xdata.mvver);
			   if(xdata.refIdx == refIndex)
			      begin
			         validCount = validCount+1;
			         mvhorPred = xdata.mvhor;
			         mvverPred = xdata.mvver;
			      end
		        end
		     else
		       begin
		          mvhorABC[ii] = 0;
			  mvverABC[ii] = 0;
                       end     
	          end
	       if(validCount != 1)//median
	          begin
		     if(mvhorABC[0]>mvhorABC[1] && mvhorABC[0]>mvhorABC[2])
		        mvhorPred = pack((mvhorABC[1]>mvhorABC[2]) ? mvhorABC[1] : mvhorABC[2]);
		     else if(mvhorABC[0]<mvhorABC[1] && mvhorABC[0]<mvhorABC[2])
		        mvhorPred = pack((mvhorABC[1]<mvhorABC[2]) ? mvhorABC[1] : mvhorABC[2]);
		     else
		        mvhorPred = pack(mvhorABC[0]);
		     if(mvverABC[0]>mvverABC[1] && mvverABC[0]>mvverABC[2])
		        mvverPred = pack((mvverABC[1]>mvverABC[2]) ? mvverABC[1] : mvverABC[2]);
		     else if(mvverABC[0]<mvverABC[1] && mvverABC[0]<mvverABC[2])
		        mvverPred = pack((mvverABC[1]<mvverABC[2]) ? mvverABC[1] : mvverABC[2]);
		     else
		        mvverPred = pack(mvverABC[0]);
	          end
	       if(interstate==InterPskip)
	          begin
		     for(Integer ii=0; ii<2; ii=ii+1)
		        begin
			   if(blockABC[ii] matches tagged BlockMv .xdata)
			      begin
			         if(xdata.refIdx==0 && xdata.mvhor==0 && xdata.mvver==0)
				    begin
				       mvhorPred = 0;
				       mvverPred = 0;
				    end
			      end
			   else if(blockABC[ii] matches tagged NotInter 0)
			      begin
			         mvhorPred = 0;
			         mvverPred = 0;
			      end
		        end
	          end
	       else if(interstate==InterP16x8 || interstate==InterP8x16)
	          begin
		     InterBlockMv blockCheck;
		     if(interstate==InterP16x8)
		        begin
			   if(interMbPartNum==0)
			      blockCheck = blockABC[1];
			   else
			      blockCheck = blockABC[0];
		        end
	             else
		        begin
			   if(interMbPartNum==0)
			      blockCheck = blockABC[0];
			   else
			      blockCheck = blockABC[2];
		        end
		     if(blockCheck matches tagged BlockMv .xdata &&& xdata.refIdx==refIndex)
		        begin
			   mvhorPred = xdata.mvhor;
			   mvverPred = xdata.mvver;
		        end
	          end
	       mvhorfinal = mvhorPred;
	       mvverfinal = mvverPred;
	       if(interstate!=InterPskip)
	          begin
		     mvhorfinal = truncate(tpl_1(interMvDiff.first()) + signExtend(mvhorPred));
		     mvverfinal = truncate(tpl_2(interMvDiff.first()) + signExtend(mvverPred));
		     interMvDiff.deq();
	          end
	       interMvFile.upd({interMbPartNum,interSubMbPartNum},tuple2(mvhorfinal,mvverfinal));
	       interNewestMvNext = zeroExtend({interMbPartNum,interSubMbPartNum})+1;
	       $display( "Trace Prediction: interProcessStep %h %h %h %h %h %h %h %h %h", interstate, interStepCount, interMbPartNum, interSubMbPartNum, pack(blockABC[0]), pack(blockABC[1]), pack(blockABC[2]), mvhorPred, mvverPred);
	    end
         else
	    begin
	       if(leftmv)
	          begin
		     if(blockABC[0] matches tagged BlockMv .xdata)
		        begin
			   mvhorfinal = unpack(xdata.mvhor);
			   mvverfinal = unpack(xdata.mvver);
		        end
		     else
		        $display( "ERROR Prediction: interProcessStep unexpected blockABC[0]");
	          end
	       else
	          begin
		     if(blockABC[1] matches tagged BlockMv .xdata)
		        begin
			   mvhorfinal = unpack(xdata.mvhor);
			   mvverfinal = unpack(xdata.mvver);
		        end
		     else
		        $display( "ERROR Prediction: interProcessStep unexpected blockABC[1]");
	          end
	    end

	    mvhorfinalR <= mvhorfinal;
	    mvverfinalR <= mvverfinal;
	    interNewestMvNextR <= interNewestMvNext;
	    interStepCount <= 3;

         end
      else // stepCount == 3
         begin
            Bit#(2) tempBShor = 0;//bS calculation
            Bit#(2) tempBSver = 0;
	    Bool allDone = False;
	    Bit#(4) refIndex = refIndexR;
	    Bit#(14) mvhorfinal = mvhorfinalR;
	    Bit#(12) mvverfinal = mvverfinalR;
	    Bit#(5) interNewestMvNext = interNewestMvNextR;

            if(interLeftVal[blockVer] matches tagged BlockMv .xdata)
	       begin
	          if(xdata.nonZeroTransCoeff == 1)
	             tempBShor = 2;
	          else
	             begin
		       if(xdata.refIdx!=refIndex || absDiffGEFour14(mvhorfinal,xdata.mvhor) || absDiffGEFour12(mvverfinal,xdata.mvver))
		           tempBShor = 1;
		       else
		           tempBShor = 0;
	             end
	       end
            else
	    tempBShor = 3;
            if(interTopVal[blockHor] matches tagged BlockMv .xdata)
	       begin
	          if(xdata.nonZeroTransCoeff == 1)
	             tempBSver = 2;
	          else
	             begin
		        if(xdata.refIdx!=refIndex || absDiffGEFour14(mvhorfinal,xdata.mvhor) || absDiffGEFour12(mvverfinal,xdata.mvver))
		           tempBSver = 1;
		        else
		           tempBSver = 0;
	             end
	       end
            else
	       tempBSver = 3;
            interBSfifo.enq(tuple2(tempBShor,tempBSver));
            Vector#(5,InterBlockMv) interTopValNext = interTopVal;//update inter*Val
            Vector#(4,InterBlockMv) interLeftValNext = interLeftVal;
            Vector#(4,InterBlockMv) interTopLeftValNext = interTopLeftVal;
            interLeftValNext[blockVer] = (BlockMv {refIdx:refIndex,mvhor:mvhorfinal,mvver:mvverfinal,nonZeroTransCoeff:0});
            interTopValNext[blockHor] = (BlockMv {refIdx:refIndex,mvhor:mvhorfinal,mvver:mvverfinal,nonZeroTransCoeff:0});
            interTopLeftValNext[blockVer] = interTopVal[blockHor];
            interTopVal <= interTopValNext;
            interLeftVal <= interLeftValNext;
            interTopLeftVal <= interTopLeftValNext;
            if(blockVer == 3)
	       interOutBlockMvfifo.enq(tagged BlockMv {refIdx:refIndex,mvhor:mvhorfinal,mvver:mvverfinal,nonZeroTransCoeff:0});
            if(interSubMbPartNum == 3)//next step
	       begin
	          interSubMbPartNum <= 0;
	          if(interMbPartNum == 3)
	             begin
		        interMbPartNum <= 0;
		        allDone = True;
		        interNewestMvNext = 16;
	             end
	          else
	             interMbPartNum <= interMbPartNum+1;
	       end
            else
	       interSubMbPartNum <= interSubMbPartNum+1;
            if(interNewestMvNext > 0)
	       interNewestMv <= interNewestMvNext;
 
            // Check to see if we are done. 
            
	    if(allDone)
	       interStepCount <= 0;
	    else
	       interStepCount <= 1;

	    $display( "Trace Prediction: interProcessStep final %h %h %h %h %h %h %h",interstate,interStepCount,interMbPartNum,interSubMbPartNum,mvhorfinal,mvverfinal,interNewestMvNext);

       end
   endrule


   rule interIPProcessStep ( interIPStepCount>0 && currMbHor<zeroExtend(picWidth) && interNewestMv>zeroExtend({interIPMbPartNum,interIPSubMbPartNum}) );
      Bit#(PicAreaSz) currMbHorTemp = currMbHor+zeroExtend(interCurrMbDiff)-1;
      Bit#(PicHeightSz) currMbVerTemp = currMbVer;
      if( currMbHorTemp >= zeroExtend(picWidth) )
	 begin
	    currMbHorTemp = currMbHorTemp-zeroExtend(picWidth);
	    currMbVerTemp = currMbVerTemp+1;
	 end
      Bit#(2) blockHor = {interIPMbPartNum[0],interIPSubMbPartNum[0]};
      Bit#(2) blockVer = {interIPMbPartNum[1],interIPSubMbPartNum[1]};
      Bit#(3) numPart = 1;
      Bit#(3) numSubPart = 1;
      Bit#(2) subMbType = 0;
      if(interstate==InterPskip || interstate==InterP16x16)
	 numPart = 1;
      else if(interstate==InterP16x8)
	 numPart = 2;
      else if(interstate==InterP8x16)
	 numPart = 2;
      else if(interstate==InterP8x8 || interstate==InterP8x8ref0)
	 begin
	    numPart = 4;
	    subMbType = interSubMbTypeVector[interIPMbPartNum];
	    numSubPart = numSubMbPart(subMbType);
	 end
      else
	 $display( "ERROR Prediction: interIPProcessStep unexpected interstate");
      Bit#(4) refIndex = ((interstate==InterPskip||interstate==InterP8x8ref0) ? 0 : interRefIdxVector[interIPMbPartNum]);
      Bit#(PicWidthSz) currMbHorT = truncate(currMbHorTemp);
      Bit#(TAdd#(PicWidthSz,2)) horTemp = {currMbHorT,blockHor};
      Bit#(TAdd#(PicHeightSz,4)) verTemp = {currMbVerTemp,blockVer,2'b00};
      IPBlockType btTemp = IP16x16;
      if(interstate==InterPskip || interstate==InterP16x16)
	 btTemp = IP16x16;
      else if(interstate==InterP16x8)
	 btTemp = IP16x8;
      else if(interstate==InterP8x16)
	 btTemp = IP8x16;
      else
	 begin
	    case(subMbType)
	       0: btTemp = IP8x8;
	       1: btTemp = IP8x4;
	       2: btTemp = IP4x8;
	       3: btTemp = IP4x4;
	    endcase
	 end
      Bit#(14) mvhorTemp = tpl_1(interMvFile.sub({interIPMbPartNum,interIPSubMbPartNum}));
      Bit#(12) mvverTemp = tpl_2(interMvFile.sub({interIPMbPartNum,interIPSubMbPartNum}));
      if(interIPStepCount == 1)
	 begin
	    if(!(interstate==InterP8x8 || interstate==InterP8x8ref0))
	       begin
		  numPart = 4;
		  Bit#(2) interIPMbPartNumTemp = interIPMbPartNum;
		  if(btTemp==IP16x16)
		     interIPMbPartNumTemp = 0;
		  else if(btTemp==IP16x8 && interIPMbPartNumTemp[0]==1)
		     interIPMbPartNumTemp = interIPMbPartNumTemp-1;
		  else if(btTemp==IP8x16 && interIPMbPartNumTemp[1]==1)
		     interIPMbPartNumTemp = interIPMbPartNumTemp-2;
		  refIndex = ((interstate==InterPskip||interstate==InterP8x8ref0) ? 0 : interRefIdxVector[interIPMbPartNumTemp]);
		  btTemp = IP8x8;
		  mvhorTemp = tpl_1(interMvFile.sub({interIPMbPartNumTemp,2'b00}));
		  mvverTemp = tpl_2(interMvFile.sub({interIPMbPartNumTemp,2'b00}));
		  interpolator.request(IPLuma {refIdx:refIndex,hor:horTemp,ver:verTemp,mvhor:mvhorTemp,mvver:mvverTemp,bt:btTemp});
	       end
	    else
	       interpolator.request(IPLuma {refIdx:refIndex,hor:horTemp,ver:verTemp,mvhor:mvhorTemp,mvver:mvverTemp,bt:btTemp});
	 end
      else
	 interpolator.request(IPChroma {refIdx:refIndex,uv:interIPStepCount[0],hor:horTemp,ver:truncate(verTemp>>1),mvhor:mvhorTemp,mvver:mvverTemp,bt:btTemp});
      if(interIPSubMbPartNum >= truncate(numSubPart-1))
	 begin
	    interIPSubMbPartNum <= 0;
	    if(interIPMbPartNum >= truncate(numPart-1))
	       begin
		  interIPMbPartNum <= 0;
		  interIPStepCount <= interIPStepCount+1;
	       end
	    else
	       begin
		  if(btTemp == IP16x8)
		     interIPMbPartNum <= 2;
		  else
		     interIPMbPartNum <= interIPMbPartNum+1;
	       end
	 end
      else
	 begin
	    if(subMbType == 1)
	       interIPSubMbPartNum <= 2;
	    else
	       interIPSubMbPartNum <= interIPSubMbPartNum+1;
	 end
      $display( "Trace Prediction: interIPProcessStep %h %h %h %h %h %h %h %h %h %h", interstate, interIPStepCount, interIPMbPartNum, interIPSubMbPartNum, refIndex, horTemp, verTemp, mvhorTemp, mvverTemp, pack(btTemp));
   endrule


   rule interDone ( interstate!=Start && interReqCount==0 && interRespCount==0 && interStepCount==0 && interIPStepCount==0 );
      interstate <= Start;
      //$display( "Trace Prediction: interOutputTransfer %h %h", interstate, interOutputCount);
   endrule

   
   rule interOutputTransfer ( True );
      predictedfifo.enq(interpolator.first());
      interpolator.deq();
      //$display( "Trace Prediction: interOutputTransfer %h %h", interstate, interOutputCount);
   endrule



   // intra prediction rules

   rule intraSendReq ( intraReqCount>0 && currMbHor<zeroExtend(picWidth) && !nextoutputfifo.notEmpty() );
      Bit#(PicWidthSz) temp2 = truncate(currMbHor);
      Bit#(TAdd#(PicWidthSz,2)) temp = 0;
      Bit#(1) noMoreReq = 0;
      if( currMb-firstMb < zeroExtend(picWidth) )
	 noMoreReq = 1;
      else
	 begin
	    if(intraReqCount<5)
	       begin
		  Bit#(2) temp3 = truncate(intraReqCount-1);
		  temp = {temp2,temp3};
	       end
	    else if(intraReqCount==5)
	       begin
		  if((currMbHor+1)<zeroExtend(picWidth) && intrastate==Intra4x4)
		     temp = {(temp2+1),2'b00};
		  else if(currMbHor>0 && currMb-firstMb>zeroExtend(picWidth))
		     temp = {(temp2-1),2'b11};
		  else
		     noMoreReq = 1;
	       end
	    else if(intraReqCount==6)
	       begin
		  if((currMbHor+1)<zeroExtend(picWidth) && intrastate==Intra4x4 && currMbHor>0 && currMb-firstMb>zeroExtend(picWidth))
		     temp = {(temp2-1),2'b11};
		  else
		     noMoreReq = 1;
	       end
	    else
	       noMoreReq = 1;
	 end
      if(noMoreReq == 0)
	 begin
      	    intraMemReqQ.enq(tagged LoadReq temp);
	    intraReqCount <= intraReqCount+1;
	    //$display( "TRACE Prediction: intraSendReq addr %0d",temp);///////////////////////
	 end
      else
	 intraReqCount <= 0;
      $display( "Trace Prediction: intraSendReq");
   endrule


   rule intraReceiveNoResp ( intraRespCount>0 && currMbHor<zeroExtend(picWidth) && currMb-firstMb<zeroExtend(picWidth) );
      intra4x4typeTop <= replicate(15);
      intraRespCount <= 0;
      intraStepCount <= 1;
      blockNum <= 0;
      pixelNum <= 0;
      interOutBlockMvfifo.enq(tagged NotInter 1);
      $display( "Trace Prediction: intraReceiveNoResp");
   endrule

   
   rule intraReceiveResp ( intraRespCount>0 && intraRespCount<7 && currMbHor<zeroExtend(picWidth) &&& intraMemRespQ.first() matches tagged LoadResp .data);
      Bit#(1) noMoreResp = 0;
      Bit#(2) temp2bit = 0;
      if(intraRespCount<5)
	 begin
	    temp2bit = truncate(intraRespCount-1);
	    intra4x4typeTop <= update(intra4x4typeTop, temp2bit, data[67:64]);
	    if(intraRespCount==4)
	       begin
		  Vector#(5,Bit#(32)) intraTopValTemp = intraTopVal;
		  intraTopValTemp[3] = data[31:0];
		  intraTopValTemp[4] = {data[31:24],data[31:24],data[31:24],data[31:24]};
		  intraTopVal <= intraTopValTemp;
		  if(!((currMbHor+1)<zeroExtend(picWidth) && intrastate==Intra4x4) && !(currMbHor>0 && currMb-firstMb>zeroExtend(picWidth)))
		     noMoreResp = 1;
	       end
	    else
	       intraTopVal <= update(intraTopVal, intraRespCount-1, data[31:0]);
	    intraTopValChroma0 <= update(intraTopValChroma0, temp2bit, data[47:32]);
	    intraTopValChroma1 <= update(intraTopValChroma1, temp2bit, data[63:48]);
	 end
      else if(intraRespCount==5)
	 begin
	    if((currMbHor+1)<zeroExtend(picWidth) && intrastate==Intra4x4)
	       begin
		  if(!(data[67:64]==15 || (data[67:64]==14 && ppsconstrained_intra_pred_flag==1)))
		     intraTopVal <= update(intraTopVal, 4, data[31:0]);
		  if(!(currMbHor>0 && currMb-firstMb>zeroExtend(picWidth)))
		     noMoreResp = 1;
	       end
	    else
	       begin
		  Bit#(40) temp2 = intraLeftVal[0];
		  intraLeftVal <= update(intraLeftVal, 0, {temp2[39:8],data[31:24]});
		  intraLeftValChroma0 <= update(intraLeftValChroma0, 0, data[47:40]);
		  intraLeftValChroma1 <= update(intraLeftValChroma1, 0, data[63:56]);
		  noMoreResp = 1;
	       end
	 end
      else
	 begin
	    Bit#(40) temp2 = intraLeftVal[0];
	    intraLeftVal <= update(intraLeftVal, 0, {temp2[39:8],data[31:24]});
	    intraLeftValChroma0 <= update(intraLeftValChroma0, 0, data[47:40]);
	    intraLeftValChroma1 <= update(intraLeftValChroma1, 0, data[63:56]);
	    noMoreResp = 1;
	 end
      intraMemRespQ.deq();
      //$display( "TRACE Prediction: intraReceiveResp data %h",data);///////////////////////
      if(noMoreResp == 0)
	 intraRespCount <= intraRespCount+1;
      else
	 begin
	    intraRespCount <= 0;
	    intraStepCount <= 1;
	    blockNum <= 0;
	    pixelNum <= 0;
	    interOutBlockMvfifo.enq(tagged NotInter 1);
	 end
      $display( "Trace Prediction: intraReceiveResp");
   endrule

   
   rule intraPredTypeStep ( intraStepCount==1 && !nextoutputfifo.notEmpty());
      Bit#(2) blockHor = {blockNum[2],blockNum[0]};
      Bit#(2) blockVer = {blockNum[3],blockNum[1]};
      Bit#(4) topType = select(intra4x4typeTop, blockHor);
      Bit#(4) leftType;
      if(currMbHor!=0 || blockNum!=0)
	 leftType = select(intra4x4typeLeft, blockVer);
      else
	 begin
	    leftType = 15;
	    intra4x4typeLeft <= replicate(15);
	 end
      if(intrastate!=Intra4x4)
	 begin
	    intraStepCount <= intraStepCount+1;
	    nextoutputfifo.enq(NonSkipMB);
	 end
      else
	 begin
	    Bit#(1) topAvailable;
	    Bit#(1) leftAvailable;
	    if(topType==15 || (topType==14 && ppsconstrained_intra_pred_flag==1))
	       topAvailable = 0;
	    else
	       topAvailable = 1;
	    if(leftType==15 || (leftType==14 && ppsconstrained_intra_pred_flag==1))
	       leftAvailable = 0;
	    else
	       leftAvailable = 1;
	    Bit#(4) predType = 0;
	    Bit#(4) remType = rem_intra4x4_pred_mode.first();
	    Bit#(4) curType = 0;
	    rem_intra4x4_pred_mode.deq();
	    if(topAvailable==0 || leftAvailable==0)
	       predType = 2;
	    else
	       begin
		  Bit#(4) topType2 = topType;
		  Bit#(4) leftType2 = leftType;
		  if(topType>8)
		     topType2 = 2;
		  if(leftType>8)
		     leftType2 = 2;
		  if(topType2 > leftType2)
		     predType = leftType2;
		  else
		     predType = topType2;
	       end
	    if(remType[3] == 1)
	       curType = predType;
	    else if(remType < predType)
	       curType = remType;
	    else
	       curType = remType+1;
	    cur_intra4x4_pred_mode <= curType;
	    intraStepCount <= intraStepCount+1;
	    if(blockNum == 15)
	       nextoutputfifo.enq(tagged Intra4x4PlusChroma);
	    else
	       nextoutputfifo.enq(tagged Intra4x4);
	    $display( "TRACE Prediction: intraPredTypeStep currMbHor currMbVer blockNum topType leftType predType remType curType %0d %0d %0d %0d %0d %0d %0d %0d",currMbHor,currMbVer,blockNum,topType,leftType,predType,remType,curType);//////////////////
	 end
      //$display( "Trace Prediction: intraPredTypeStep");
   endrule


   rule intraProcessStep ( intraStepCount>1 );
      $display( "TRACE Prediction: intraProcessStep %0d %0d", blockNum, pixelNum);////////////////////
      //$display( "TRACE Prediction: intraProcessStep intraTopVal %h %h %h %h %h",intraTopVal[4],intraTopVal[3],intraTopVal[2],intraTopVal[1],intraTopVal[0]);/////////////////
      Bit#(1) outFlag  = 0;
      Bit#(4) nextIntraStepCount = intraStepCount+1;
      Bit#(2) blockHor = {blockNum[2],blockNum[0]};
      Bit#(2) blockVer = {blockNum[3],blockNum[1]};
      Bit#(2) pixelVer = {pixelNum[3],pixelNum[2]};
      Vector#(4,Bit#(8)) predVector = replicate(0);

      Bit#(4) topType = select(intra4x4typeTop, blockHor);
      Bit#(4) leftType = select(intra4x4typeLeft, blockVer);
      Bit#(1) topAvailable;
      Bit#(1) leftAvailable;
      if(topType==15 || (topType==14 && ppsconstrained_intra_pred_flag==1))
	 topAvailable = 0;
      else
	 topAvailable = 1;
      if(leftType==15 || (leftType==14 && ppsconstrained_intra_pred_flag==1))
	 leftAvailable = 0;
      else
	 leftAvailable = 1;
      if(blockNum==0 && pixelNum==0 && intraChromaFlag==0)
	 begin
	    intraChromaTopAvailable <= topAvailable;
	    intraChromaLeftAvailable <= leftAvailable;
	 end
      if(intrastate==Intra4x4 && intraChromaFlag==0)
	 begin
	    if(intraStepCount==2)
	       begin
		  outFlag = 1;
		  Bit#(40) leftValSet = select(intraLeftVal,blockVer);
		  Bit#(32) topMidValSet = select(intraTopVal,blockHor);
		  Bit#(32) topRightValSet = select(intraTopVal,{1'b0,blockHor}+1);
		  Bit#(72) topValSet;
		  if((blockNum[3:2]==3 && blockNum[0]==1) || blockNum[1:0]==3)
		     topValSet = {topMidValSet[31:24],topMidValSet[31:24],topMidValSet[31:24],topMidValSet[31:24],topMidValSet,leftValSet[7:0]};
		  else
		     topValSet = {topRightValSet,topMidValSet,leftValSet[7:0]};
		  $display( "TRACE Prediction: intraProcessStep intra4x4 %0d %0d %h %h", cur_intra4x4_pred_mode, blockNum, leftValSet, topValSet);////////////////////
		  Bit#(4) topSelect1 = 0;
		  Bit#(4) topSelect2 = 0;
		  Bit#(4) topSelect3 = 0;
		  Bit#(3) leftSelect1 = 0;
		  Bit#(3) leftSelect2 = 0;
		  Bit#(3) leftSelect3 = 0;
		  Bit#(10) tempVal1 = 0;
		  Bit#(10) tempVal2 = 0;
		  Bit#(10) tempVal3 = 0;
		  case(cur_intra4x4_pred_mode)
		     0://vertical
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      topSelect1 = fromInteger(pixelHor);
			      Bit#(8) topVal = intra4x4SelectTop(topValSet,topSelect1);
			      predVector[pixelHor] = topVal;
			   end
		     end
		     1://horizontal
		     begin
			leftSelect1 = zeroExtend(pixelVer);
			Bit#(8) leftVal = intra4x4SelectLeft(leftValSet,leftSelect1);
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   predVector[pixelHor] = leftVal;
		     end
		     2://dc
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(10) tempTopSum = zeroExtend(topValSet[15:8])+zeroExtend(topValSet[23:16])+zeroExtend(topValSet[31:24])+zeroExtend(topValSet[39:32]) + 2;
			      Bit#(10) tempLeftSum = zeroExtend(leftValSet[15:8])+zeroExtend(leftValSet[23:16])+zeroExtend(leftValSet[31:24])+zeroExtend(leftValSet[39:32]) + 2;
			      Bit#(11) tempTotalSum = zeroExtend(tempTopSum)+zeroExtend(tempLeftSum);
			      Bit#(8) topSum = tempTopSum[9:2];
			      Bit#(8) leftSum = tempLeftSum[9:2];
			      Bit#(8) totalSum = tempTotalSum[10:3];
			      if(topAvailable==1 && leftAvailable==1)
				 predVector[pixelHor] = totalSum;
			      else if(topAvailable==1)
				 predVector[pixelHor] = topSum;
			      else if(leftAvailable==1)
				 predVector[pixelHor] = leftSum;
			      else
				 predVector[pixelHor] = 8'b10000000;
			   end
		     end
		     3://diagonal down left
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(4) selectNum = fromInteger(pixelHor)+zeroExtend(pixelVer);
			      if(pixelHor==3 && pixelVer==3)
				 begin
				    topSelect1 = 6;
				    topSelect2 = 7;
				    topSelect3 = 7;
				 end
			      else
				 begin
				    topSelect1 = selectNum;
				    topSelect2 = selectNum+1;
				    topSelect3 = selectNum+2;
				 end
			      tempVal1 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
			      tempVal2 = zeroExtend(intra4x4SelectTop(topValSet,topSelect2));
			      tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect3));
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     4://diagonal down right
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      if(fromInteger(pixelHor) > pixelVer)
				 begin
				    topSelect3 = fromInteger(pixelHor)-zeroExtend(pixelVer);
				    topSelect2 = topSelect3-1;
				    topSelect1 = topSelect3-2;
				    tempVal1 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectTop(topValSet,topSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect3));
				 end
			      else if(fromInteger(pixelHor) < pixelVer)
				 begin
				    leftSelect3 = zeroExtend(pixelVer)-fromInteger(pixelHor);
				    leftSelect2 = leftSelect3-1;
				    leftSelect1 = leftSelect3-2;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect3));
				 end
			      else
				 begin
				    leftSelect1 = 0;
				    leftSelect2 = -1;
				    topSelect1 = 0;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				 end
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     5://vertical right
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(4) tempPixelHor = fromInteger(pixelHor);
			      Bit#(4) zVR = (tempPixelHor<<1)-zeroExtend(pixelVer);
			      if(zVR<=6 && zVR>=0)
				 begin
				    topSelect3 = fromInteger(pixelHor)-zeroExtend(pixelVer>>1);
				    topSelect2 = topSelect3-1;
				    if(zVR==1 || zVR==3 || zVR==5)
				       topSelect1 = topSelect3-2;
				    else
				       topSelect1 = topSelect3;
				    tempVal1 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectTop(topValSet,topSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect3));
				 end
			      else if(zVR==-1)
				 begin
				    leftSelect1 = 0;
				    leftSelect2 = -1;
				    topSelect1 = 0;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				 end
			      else
				 begin
				    leftSelect1 = zeroExtend(pixelVer)-1;
				    leftSelect2 = leftSelect1-1;
				    leftSelect3 = leftSelect1-2;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect3));
				 end
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     6://horizontal down
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(4) tempPixelVer = zeroExtend(pixelVer);
			      Bit#(4) zHD = (tempPixelVer<<1)-fromInteger(pixelHor);
			      if(zHD<=6 && zHD>=0)
				 begin
				    leftSelect3 = zeroExtend(pixelVer)-fromInteger(pixelHor/2);
				    leftSelect2 = leftSelect3-1;
				    if(zHD==1 || zHD==3 || zHD==5)
				       leftSelect1 = leftSelect3-2;
				    else
				       leftSelect1 = leftSelect3;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect3));
				 end
			      else if(zHD==-1)
				 begin
				    leftSelect1 = 0;
				    leftSelect2 = -1;
				    topSelect1 = 0;
				    tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				 end
			      else
				 begin
				    topSelect1 = fromInteger(pixelHor)-1;
				    topSelect2 = topSelect1-1;
				    topSelect3 = topSelect1-2;
				    tempVal1 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
				    tempVal2 = zeroExtend(intra4x4SelectTop(topValSet,topSelect2));
				    tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect3));
				 end
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     7://vertical left
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      topSelect1 = fromInteger(pixelHor)+zeroExtend(pixelVer>>1);
			      topSelect2 = topSelect1+1;
			      if(pixelVer==1 || pixelVer==3)
				 topSelect3 = topSelect1+2;
			      else
				 topSelect3 = topSelect1;
			      tempVal1 = zeroExtend(intra4x4SelectTop(topValSet,topSelect1));
			      tempVal2 = zeroExtend(intra4x4SelectTop(topValSet,topSelect2));
			      tempVal3 = zeroExtend(intra4x4SelectTop(topValSet,topSelect3));
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     8://horizontal up
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(4) tempPixelVer = zeroExtend(pixelVer);
			      Bit#(4) zHU = (tempPixelVer<<1)+fromInteger(pixelHor);
			      if(zHU<=4)
				 begin
				    leftSelect1 = zeroExtend(pixelVer)+fromInteger(pixelHor/2);
				    leftSelect2 = leftSelect1+1;
				    if(zHU==1 || zHU==3)
				       leftSelect3 = leftSelect1+2;
				    else
				       leftSelect3 = leftSelect1;
				 end
			      else
				 begin
				    if(zHU==5)
				       leftSelect1 = 2;
				    else
				       leftSelect1 = 3;
				    leftSelect2 = 3;
				    leftSelect3 = 3;
				 end
			      tempVal1 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect1));
			      tempVal2 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect2));
			      tempVal3 = zeroExtend(intra4x4SelectLeft(leftValSet,leftSelect3));
			      Bit#(10) predVal = tempVal1 + (tempVal2<<1) + tempVal3 + 2;
			      predVector[pixelHor] = predVal[9:2];
			   end
		     end
		     default: $display( "ERROR Prediction: intraProcessStep intra4x4 unknown cur_intra4x4_pred_mode");
		  endcase
	       end
	    else
	       $display( "ERROR Prediction: intraProcessStep intra4x4 unknown intraStepCount");
	 end
      else if(intrastate==Intra16x16  && intraChromaFlag==0)
	 begin
	    //$display( "TRACE Prediction: intraProcessStep intra16x16 %0d %0d %0d %h", intra16x16_pred_mode, currMb, blockNum, select(intraTopVal,blockHor));/////////////////
	    case(intra16x16_pred_mode)
	       0://vertical
	       begin
		  for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
		     begin
			Bit#(32) topValSet = select(intraTopVal,blockHor);
			Bit#(8) topVal = select32to8(topValSet,fromInteger(pixelHor));
			predVector[pixelHor] = topVal;
		     end
		  outFlag = 1;
	       end
	       1://horizontal
	       begin
		  Bit#(40) leftValSet = select(intraLeftVal,blockVer);
		  Bit#(8) leftVal = intra4x4SelectLeft(leftValSet,zeroExtend(pixelVer));
		  for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
		     predVector[pixelHor] = leftVal;
		  outFlag = 1;
	       end
	       2://dc
	       begin
		  case(intraStepCount)
		     2:
		     begin
			if(topAvailable == 1)
			   begin
			      Bit#(32) topValSet = select(intraTopVal,0);
			      intraSumA <= zeroExtend(topValSet[7:0])+zeroExtend(topValSet[15:8])+zeroExtend(topValSet[23:16])+zeroExtend(topValSet[31:24]);
			   end
			else
			   begin
			      intraSumA <= 0;
			      nextIntraStepCount = 6;
			   end
		     end
		     3:
		     begin
			Bit#(32) topValSet = select(intraTopVal,1);
			intraSumA <= intraSumA+zeroExtend(topValSet[7:0])+zeroExtend(topValSet[15:8])+zeroExtend(topValSet[23:16])+zeroExtend(topValSet[31:24]);
		     end
		     4:
		     begin
			Bit#(32) topValSet = select(intraTopVal,2);
			intraSumA <= intraSumA+zeroExtend(topValSet[7:0])+zeroExtend(topValSet[15:8])+zeroExtend(topValSet[23:16])+zeroExtend(topValSet[31:24]);
		     end
		     5:
		     begin
			Bit#(32) topValSet = select(intraTopVal,3);
			intraSumA <= intraSumA+zeroExtend(topValSet[7:0])+zeroExtend(topValSet[15:8])+zeroExtend(topValSet[23:16])+zeroExtend(topValSet[31:24])+8;
		     end
		     6:
		     begin
			if(leftAvailable == 1)
			   begin
			      Bit#(40) leftValSet = select(intraLeftVal,0);
			      intraSumA <= intraSumA+zeroExtend(leftValSet[15:8])+zeroExtend(leftValSet[23:16])+zeroExtend(leftValSet[31:24])+zeroExtend(leftValSet[39:32]);
			   end
			else
			   nextIntraStepCount = 10;
		     end
		     7:
		     begin
			Bit#(40) leftValSet = select(intraLeftVal,1);
			intraSumA <= intraSumA+zeroExtend(leftValSet[15:8])+zeroExtend(leftValSet[23:16])+zeroExtend(leftValSet[31:24])+zeroExtend(leftValSet[39:32]);
		     end
		     8:
		     begin
			Bit#(40) leftValSet = select(intraLeftVal,2);
			intraSumA <= intraSumA+zeroExtend(leftValSet[15:8])+zeroExtend(leftValSet[23:16])+zeroExtend(leftValSet[31:24])+zeroExtend(leftValSet[39:32]);
		     end
		     9:
		     begin
			Bit#(40) leftValSet = select(intraLeftVal,3);
			intraSumA <= intraSumA+zeroExtend(leftValSet[15:8])+zeroExtend(leftValSet[23:16])+zeroExtend(leftValSet[31:24])+zeroExtend(leftValSet[39:32])+8;
		     end
		     10:
		     begin
			if(leftAvailable == 1 && topAvailable == 1)
			   intraSumA <= intraSumA >> 5;
			else if(leftAvailable == 1 || topAvailable == 1)
			   intraSumA <= intraSumA >> 4;
			else
			   intraSumA <= 128;
		     end
		     11:
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   predVector[pixelHor] = intraSumA[7:0];
			outFlag = 1;
		     end
		     default: $display( "ERROR Prediction: intraProcessStep intra16x16 DC unknown intraStepCount");
		  endcase
	       end
	       3://plane
	       begin
		  if(intraStepCount == 2)
		     begin
			Bit#(32) topValSet = select(intraTopVal,3);
			Bit#(8) topVal = select32to8(topValSet,3);
			Bit#(40) leftValSet = select(intraLeftVal,3);
			Bit#(8) leftVal = intra4x4SelectLeft(leftValSet,3);
			Bit#(13) tempVal = zeroExtend(topVal) + zeroExtend(leftVal);
			intraSumA <= tempVal << 4;
			intraSumB <= 0;
			intraSumC <= 0;
		     end
		  else if(intraStepCount < 11)
		     begin
			Bit#(4) xyPlusOne = intraStepCount-2;
			Bit#(4) xyPlusEight = intraStepCount+5;
			Bit#(4) sixMinusXY = 9-intraStepCount;
			Bit#(32) topValSet1 = select(intraTopVal,xyPlusEight[3:2]);
			Bit#(8) topVal1 = select32to8(topValSet1,xyPlusEight[1:0]);
			Bit#(40) leftValSet1 = select(intraLeftVal,xyPlusEight[3:2]);
			Bit#(8) leftVal1 = intra4x4SelectLeft(leftValSet1,zeroExtend(xyPlusEight[1:0]));
			Bit#(32) topValSet2=0;
			Bit#(8) topVal2;
			Bit#(40) leftValSet2;
			Bit#(8) leftVal2;
			if(intraStepCount==10)
			   begin
			      leftValSet2 = select(intraLeftVal,0);
			      leftVal2 = intra4x4SelectLeft(leftValSet2,-1);
			      topVal2 = leftVal2;
			   end
			else
			   begin
			      topValSet2 = select(intraTopVal,sixMinusXY[3:2]);
			      topVal2 = select32to8(topValSet2,sixMinusXY[1:0]);
			      leftValSet2 = select(intraLeftVal,sixMinusXY[3:2]);
			      leftVal2 = intra4x4SelectLeft(leftValSet2,zeroExtend(sixMinusXY[1:0]));
			   end
			Bit#(15) diffH = zeroExtend(topVal1) - zeroExtend(topVal2);
			Bit#(15) diffV = zeroExtend(leftVal1) - zeroExtend(leftVal2);
			intraSumB <= intraSumB + (zeroExtend(xyPlusOne) * diffH);
			intraSumC <= intraSumC + (zeroExtend(xyPlusOne) * diffV);
		     end
		  else if(intraStepCount == 11)
		     begin
			Bit#(18) tempSumB = (5*signExtend(intraSumB)) + 32;
			Bit#(18) tempSumC = (5*signExtend(intraSumC)) + 32;
			intraSumB <= signExtend(tempSumB[17:6]);
			intraSumC <= signExtend(tempSumC[17:6]);
		     end
		  else if(intraStepCount == 12)
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(5)  positionHor = {1'b0,blockHor,fromInteger(pixelHor)};
			      Bit#(5)  positionVer = {1'b0,blockVer,pixelVer};
			      Bit#(16) tempProductB = signExtend(intraSumB) * signExtend(positionHor-7);
			      Bit#(16) tempProductC = signExtend(intraSumC) * signExtend(positionVer-7);
			      Bit#(16) tempTotal = tempProductB + tempProductC + zeroExtend(intraSumA) + 16;
			      if(tempTotal[15]==1)
				 predVector[pixelHor] = 0;
			      else if(tempTotal[14:5] > 255)
				 predVector[pixelHor] = 255;
			      else
				 predVector[pixelHor] = tempTotal[12:5];
			   end
			outFlag = 1;
		     end
		  else
		     $display( "ERROR Prediction: intraProcessStep intra16x16 plane unknown intraStepCount");
	       end
	    endcase
	 end
      else if(intraChromaFlag==1)
	 begin
	    //$display( "TRACE Prediction: intraProcessStep intraChroma %0d %0d %0d %0d %0d %0d %h %h %h %h %h %h %h %h",intra_chroma_pred_mode.first(),intraChromaTopAvailable,intraChromaLeftAvailable,currMb,blockNum,pixelNum,pack(intraLeftValChroma0),pack(intraTopValChroma0),pack(intraLeftValChroma1),pack(intraTopValChroma1),intraLeftValChroma0[0],intraTopValChroma0[3][15:8],intraLeftValChroma1[0],intraTopValChroma1[3][15:8]);///////////////////
	    Vector#(9,Bit#(8)) tempLeftVec;
	    Vector#(4,Bit#(16)) tempTopVec;
	    if(blockNum[2] == 0)
	       begin
		  tempLeftVec = intraLeftValChroma0;
		  tempTopVec = intraTopValChroma0;
	       end
	    else
	       begin
		  tempLeftVec = intraLeftValChroma1;
		  tempTopVec = intraTopValChroma1;
	       end
	    case(intra_chroma_pred_mode.first())
	       0://dc
	       begin
		  if(intraStepCount == 2)
		     begin
			Bit#(1) useTop=0;
			Bit#(1) useLeft=0;
			if(blockNum[1:0] == 0 || blockNum[1:0] == 3)
			   begin
			      useTop = intraChromaTopAvailable;
			      useLeft = intraChromaLeftAvailable;
			   end
			else if(blockNum[1:0] == 1)
			   begin
			      if(intraChromaTopAvailable == 1)
				 useTop = 1;
			      else if(intraChromaLeftAvailable == 1)
				 useLeft = 1;
			   end
			      else if(blockNum[1:0] == 2)
				 begin
				    if(intraChromaLeftAvailable == 1)
				       useLeft = 1;
				    else if(intraChromaTopAvailable == 1)
				       useTop = 1;
				 end
		        else
			   $display( "ERROR Prediction: intraProcessStep intraChroma dc unknown blockNum");
			Bit#(10) topSum;
			Bit#(10) leftSum;
			Bit#(11) totalSum;
			if(blockHor[0] == 0)
			   topSum = zeroExtend(tempTopVec[0][15:8])+zeroExtend(tempTopVec[0][7:0])+zeroExtend(tempTopVec[1][15:8])+zeroExtend(tempTopVec[1][7:0])+2;
			else
			   topSum = zeroExtend(tempTopVec[2][15:8])+zeroExtend(tempTopVec[2][7:0])+zeroExtend(tempTopVec[3][15:8])+zeroExtend(tempTopVec[3][7:0])+2;
			if(blockVer[0] == 0)
			   leftSum = zeroExtend(tempLeftVec[1])+zeroExtend(tempLeftVec[2])+zeroExtend(tempLeftVec[3])+zeroExtend(tempLeftVec[4])+2;
			else
			   leftSum = zeroExtend(tempLeftVec[5])+zeroExtend(tempLeftVec[6])+zeroExtend(tempLeftVec[7])+zeroExtend(tempLeftVec[8])+2;
			totalSum = zeroExtend(topSum) + zeroExtend(leftSum);
			if(useTop==1 && useLeft==1)
			   intraSumA <= zeroExtend(totalSum[10:3]);
			else if(useTop==1)
			   intraSumA <= zeroExtend(topSum[9:2]);
			else if(useLeft==1)
			   intraSumA <= zeroExtend(leftSum[9:2]);
			else
			   intraSumA <= zeroExtend(8'b10000000);
		     end
		  else if(intraStepCount == 3)
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   predVector[pixelHor] = intraSumA[7:0];
			outFlag = 1;
		     end
		  else
		     $display( "ERROR Prediction: intraProcessStep intraChroma dc unknown intraStepCount");
	       end
	       1://horizontal
	       begin
		  for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
		     begin
			Bit#(4) tempLeftIdx = {1'b0,blockVer[0],pixelVer} + 1;
			predVector[pixelHor] = select(tempLeftVec,tempLeftIdx);
		     end
		  outFlag = 1;
	       end
	       2://vertical
	       begin
		  for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
		     begin
			Bit#(2) pixelHorTemp = fromInteger(pixelHor);
			Bit#(16) tempTopVal = select(tempTopVec,{blockHor[0],pixelHorTemp[1]});
			if(pixelHorTemp[0] == 0)
			   predVector[pixelHor] = tempTopVal[7:0];
			else
			   predVector[pixelHor] = tempTopVal[15:8];
		     end
		  outFlag = 1;
	       end
	       3://plane
	       begin
		  if(intraStepCount == 2)
		     begin
			Bit#(16) topValSet = tempTopVec[3];
			Bit#(8) topVal = topValSet[15:8];
			Bit#(8) leftVal = tempLeftVec[8];
			Bit#(13) tempVal = zeroExtend(topVal) + zeroExtend(leftVal);
			intraSumA <= tempVal << 4;
			intraSumB <= 0;
			intraSumC <= 0;
		     end
		  else if(intraStepCount < 7)
		     begin
			Bit#(3) xyPlusOne = truncate(intraStepCount)-2;
			Bit#(3) xyPlusFour = truncate(intraStepCount)+1;
			Bit#(4) twoMinusXY = 5-intraStepCount;
			Bit#(16) topValSet1 = select(tempTopVec,xyPlusFour[2:1]);
			Bit#(8) topVal1 = select16to8(topValSet1,xyPlusFour[0]);
			Bit#(4) tempLeftIdx1 = {1'b0,xyPlusFour} + 1;
			Bit#(8) leftVal1 = select(tempLeftVec,tempLeftIdx1);
			
			Bit#(16) topValSet2 = select(tempTopVec,twoMinusXY[2:1]);
			Bit#(8) topVal2;
			Bit#(8) leftVal2 = select(tempLeftVec,twoMinusXY+1);
			if(intraStepCount==6)
			   topVal2 = leftVal2;
			else
			   topVal2 = select16to8(topValSet2,twoMinusXY[0]);
			Bit#(15) diffH = zeroExtend(topVal1) - zeroExtend(topVal2);
			Bit#(15) diffV = zeroExtend(leftVal1) - zeroExtend(leftVal2);
			intraSumB <= intraSumB + (zeroExtend(xyPlusOne) * diffH);
			intraSumC <= intraSumC + (zeroExtend(xyPlusOne) * diffV);
			Int#(15) tempDisplayH = unpack(zeroExtend(xyPlusOne) * diffH);
			Int#(15) tempDisplayV = unpack(zeroExtend(xyPlusOne) * diffV);
			//$display( "TRACE Prediction: intraProcessStep intraChroma plane partH partV %0d %0d",tempDisplayH,tempDisplayV);////////////////////
		     end
		  else if(intraStepCount == 7)
		     begin
			Int#(15) tempDisplayH = unpack(intraSumB);
			Int#(15) tempDisplayV = unpack(intraSumC);
			//$display( "TRACE Prediction: intraProcessStep intraChroma plane H V %0d %0d",tempDisplayH,tempDisplayV);////////////////////
			Bit#(19) tempSumB = (34*signExtend(intraSumB)) + 32;
			Bit#(19) tempSumC = (34*signExtend(intraSumC)) + 32;
			intraSumB <= signExtend(tempSumB[18:6]);
			intraSumC <= signExtend(tempSumC[18:6]);
		     end
		  else if(intraStepCount == 8)
		     begin
			for(Integer pixelHor=0; pixelHor<4; pixelHor=pixelHor+1)
			   begin
			      Bit#(4)  positionHor = {1'b0,blockHor[0],fromInteger(pixelHor)};
			      Bit#(4)  positionVer = {1'b0,blockVer[0],pixelVer};
			      Bit#(17) tempProductB = signExtend(intraSumB) * signExtend(positionHor-3);
			      Bit#(17) tempProductC = signExtend(intraSumC) * signExtend(positionVer-3);
			      Bit#(17) tempTotal = tempProductB + tempProductC + zeroExtend(intraSumA) + 16;
			      if(tempTotal[16]==1)
				 predVector[pixelHor] = 0;
			      else if(tempTotal[15:5] > 255)
				 predVector[pixelHor] = 255;
			      else
				 predVector[pixelHor] = tempTotal[12:5];
			   end
			outFlag = 1;
		     end
		  else
		     $display( "ERROR Prediction: intraProcessStep intraChroma plane unknown intraStepCount");
	       end
	    endcase
	 end
      else
	 $display( "ERROR Prediction: intraProcessStep unknown intrastate");

      if(outFlag==1)
	 begin
	    predictedfifo.enq(predVector);
	    pixelNum <= pixelNum+4;
	    if(pixelNum == 12)
	       begin
		  if(intraChromaFlag==0)
		     begin
			blockNum <= blockNum+1;
			if(blockNum == 15)
			   begin
			      intraChromaFlag <= 1;
			      intraStepCount <= 2;
			   end
			else if(intrastate==Intra4x4)
			   intraStepCount <= 1;
		     end
		  else
		     begin
			if(blockNum == 7)
			   begin
			      blockNum <= 0;
			      intraChromaFlag <= 0;
			      intraStepCount <= 0;
			      intra_chroma_pred_mode.deq();
			   end
			else
			   begin
			      blockNum <= blockNum+1;
			      if(intra_chroma_pred_mode.first()==0)
				 intraStepCount <= 2;
			      else if(blockNum==3)
				 intraStepCount <= 2;
			   end
		     end
	       end
	 end
      else
	 intraStepCount <= nextIntraStepCount;
      //$display( "Trace Prediction: intraProcessStep");
   endrule

   
   
   interface Client mem_client_intra;
      interface Get request  = fifoToGet(intraMemReqQ);
      interface Put response = fifoToPut(intraMemRespQ);
   endinterface
   interface Client mem_client_inter;
      interface Get request  = fifoToGet(interMemReqQ);
      interface Put response = fifoToPut(interMemRespQ);
   endinterface
   interface Client mem_client_buffer = interpolator.mem_client;

   interface Put ioin  = fifoToPut(infifo);
   interface Put ioin_InverseTrans  = fifoToPut(infifo_ITB);
   interface Get ioout = fifoToGet(outfifo);

      
endmodule

endpackage
