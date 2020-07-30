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
// Deblocking Filter
//----------------------------------------------------------------------
//     
//

package mkDeblockFilter;

import H264Types::*;

import IDeblockFilter::*;
import FIFO::*;
import FIFOF::*;
import Vector::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;
import RegFile::*;

//-----------------------------------------------------------
// Local Datatypes
//-----------------------------------------------------------


typedef enum                
{
  Passing,          //not working on anything in particular
  Initialize,
  Horizontal,
  Cleanup,
  HorizontalCleanup,
  Vertical
}
Process deriving(Eq,Bits);

typedef enum
{
  NormalOperation,
  VerticalCleanup
}
VerticalState deriving(Eq,Bits);

//-----------------------------------------------------------
// Helper functions


function Bit#(8) absdiff8(Bit#(8) in0, Bit#(8) in1);
   return (in1>=in0 ? in1-in0 : in0-in1);
endfunction


function Bool filter_test(Bit#(32) in_pixels, Bit#(8) alpha, Bit#(5) beta);
   Bit#(8) p1 = in_pixels[7:0];
   Bit#(8) p0 = in_pixels[15:8];
   Bit#(8) q0 = in_pixels[23:16];
   Bit#(8) q1 = in_pixels[31:24];
   return((absdiff8(p0,q0) < alpha) && 
          (absdiff8(p0,p1) < zeroExtend(beta))  &&
          (absdiff8(q0,q1) < zeroExtend(beta)));
endfunction


function Bit#(6) clip3symmetric9to6(Bit#(9) val, Bit#(5) bound);
   Int#(9) intval = unpack(val);
   Int#(6) intbound = unpack({1'b0,bound});
   Int#(6) intout = (intval<signExtend(-intbound) ? -intbound : (intval>signExtend(intbound) ? intbound : truncate(intval)));
   return pack(intout);
endfunction


function Bit#(64) filter_input(Bit#(64) in_pixels, Bool chroma_flag, Bit#(3) bs, Bit#(8) alpha, Bit#(5) beta, Vector#(3,Bit#(5)) tc0_vector);
   Bit#(8) p[4];
   Bit#(8) q[4];
   p[3] = in_pixels[7:0];
   p[2] = in_pixels[15:8];
   p[1] = in_pixels[23:16];
   p[0] = in_pixels[31:24];
   q[0] = in_pixels[39:32];
   q[1] = in_pixels[47:40];
   q[2] = in_pixels[55:48];
   q[3] = in_pixels[63:56];
   Bit#(8) p_out[4];
   Bit#(8) q_out[4];
   Bool a_p_test = absdiff8(p[2],p[0]) < zeroExtend(beta);
   Bool a_q_test = absdiff8(q[2],q[0]) < zeroExtend(beta);
   Bit#(9) p0q0 = zeroExtend(p[0])+zeroExtend(q[0]);
   if (bs == 4)
      begin
	 Bool small_gap_test = absdiff8(p[0],q[0]) < (alpha >> 2)+2;
	 Bit#(11) p_outtemp[3];
	 Bit#(11) q_outtemp[3];
	 if (!chroma_flag && a_p_test && small_gap_test)
	    begin
	       Bit#(11) sum = zeroExtend(p[1])+zeroExtend(p0q0);
	       p_outtemp[0] = (zeroExtend(p[2]) + (sum<<1) + zeroExtend(q[1]) + 4) >> 3;
	       p_outtemp[1] = (zeroExtend(p[2]) + sum + 2) >> 2;
	       p_outtemp[2] = (((zeroExtend(p[3])+zeroExtend(p[2]))<<1) + zeroExtend(p[2]) + sum + 4) >> 3;
	    end
	 else
	    begin
	       p_outtemp[0] = ((zeroExtend(p[1])<<1) + zeroExtend(p[0]) + zeroExtend(q[1]) + 2) >> 2;
	       p_outtemp[1] = zeroExtend(p[1]);
	       p_outtemp[2] = zeroExtend(p[2]);
	    end
	 if (!chroma_flag && a_q_test && small_gap_test)
	    begin
	       Bit#(11) sum = zeroExtend(q[1])+zeroExtend(p0q0);
	       q_outtemp[0] = (zeroExtend(p[1]) + (sum<<1) + zeroExtend(q[2]) + 4) >> 3;
	       q_outtemp[1] = (zeroExtend(q[2]) + sum + 2) >> 2;
	       q_outtemp[2] = (((zeroExtend(q[3])+zeroExtend(q[2]))<<1) + zeroExtend(q[2]) + sum + 4) >> 3;
	    end
	 else
	    begin
	       q_outtemp[0] = ((zeroExtend(q[1])<<1) + zeroExtend(q[0]) + zeroExtend(p[1]) + 2) >> 2;
	       q_outtemp[1] = zeroExtend(q[1]);
	       q_outtemp[2] = zeroExtend(q[2]);
	    end
	 p_out[0] = truncate(p_outtemp[0]);
	 p_out[1] = truncate(p_outtemp[1]);
	 p_out[2] = truncate(p_outtemp[2]);
	 q_out[0] = truncate(q_outtemp[0]);
	 q_out[1] = truncate(q_outtemp[1]);
	 q_out[2] = truncate(q_outtemp[2]);
      end
   else if(bs > 0)
      begin
	 Bit#(5) t_c0 = tc0_vector[bs-1];
	 Bit#(5) t_c = chroma_flag ? t_c0+1 : t_c0 + (a_p_test ? 1:0) + (a_q_test ? 1:0);
	 Bit#(12) deltatemp = (((zeroExtend(q[0])-zeroExtend(p[0]))<<2)+zeroExtend(p[1])-zeroExtend(q[1])+4);
	 Bit#(6) delta = clip3symmetric9to6(deltatemp[11:3],t_c);
	 
	 Bit#(10) p_out0temp = zeroExtend(p[0]) + signExtend(delta);
	 p_out[0] = (p_out0temp[9]==1 ? 0 : (p_out0temp[8]==1 ? 255 : p_out0temp[7:0]));
	 Bit#(10) q_out0temp = zeroExtend(q[0]) - signExtend(delta);
	 q_out[0] = (q_out0temp[9]==1 ? 0 : (q_out0temp[8]==1 ? 255 : q_out0temp[7:0]));
	 
	 Bit#(9) p0q0PLUS1 = p0q0+1;
	 Bit#(8) p0q0_av = p0q0PLUS1[8:1];
	 if (!chroma_flag && a_p_test)
	    begin
	       Bit#(10) p_out1temp = zeroExtend(p[2]) + zeroExtend(p0q0_av) - (zeroExtend(p[1])<<1);
	       p_out[1] = p[1]+signExtend(clip3symmetric9to6(p_out1temp[9:1],t_c0));
	    end
	 else
	    p_out[1] = p[1];
	 
	 if (!chroma_flag && a_q_test)
	    begin
	       Bit#(10) q_out1temp = zeroExtend(q[2]) + zeroExtend(p0q0_av) - (zeroExtend(q[1])<<1);
	       q_out[1] = q[1]+signExtend(clip3symmetric9to6(q_out1temp[9:1],t_c0));
	    end
	 else
	    q_out[1] = q[1];
	 
	 p_out[2] = p[2];
	 q_out[2] = q[2];
      end
   else
      begin
	 p_out[0] = p[0];
	 q_out[0] = q[0];
	 p_out[1] = p[1];
	 q_out[1] = q[1];
	 p_out[2] = p[2];
	 q_out[2] = q[2];
      end
   p_out[3] = p[3];
   q_out[3] = q[3];
   return({q_out[3], q_out[2], q_out[1], q_out[0], p_out[0], p_out[1], p_out[2], p_out[3]});
endfunction





//-----------------------------------------------------------
// Deblocking Filter Module
//-----------------------------------------------------------


//-----------------------------------------------------------
// 1 read port register file module

interface RFileSingle#(type idx_t, type d_t);
   method Action upd(idx_t x1, d_t x2);
   method ActionValue#(d_t) sub(idx_t x1);
endinterface

module mkRFileSingle#( idx_t lo, idx_t hi ) ( RFileSingle#(idx_t, d_t) )
   provisos (Bits#(idx_t, si),Bits#(d_t, sa));
   RegFile#(idx_t,d_t) rf <- mkRegFileWCF(lo,hi);
   RWire#(Bit#(0)) sched_hack <- mkRWire();
   method Action upd( idx_t index, d_t data );
      rf.upd( index, data );
   endmethod
   method ActionValue#(d_t) sub( idx_t index );
      sched_hack.wset(0);
      return rf.sub(index);
   endmethod
endmodule
   
module mkRFileSingleFull( RFileSingle#(idx_t, d_t) )
   provisos (Bits#(idx_t, si),Bits#(d_t, sa),Bounded#(idx_t),Literal#(idx_t) );
   RegFile#(idx_t,d_t) rf <- mkRegFileWCF(0,fromInteger(valueof(TSub#(TExp#(si),1))));
   RWire#(Bit#(0)) sched_hack <- mkRWire();
   method Action upd( idx_t index, d_t data );
      rf.upd( index, data );
   endmethod
   method ActionValue#(d_t) sub( idx_t index );
      sched_hack.wset(0);
      return rf.sub(index);
   endmethod
endmodule


interface ILeftVector;
  method ActionValue#(Bit#(32)) sub(Bit#(5) addr); 
  method Action upd(Bit#(5) addr, Bit#(32) data);
endinterface
 
(*synthesize*)
module mkLeftVector(ILeftVector);
  RFileSingle#(Bit#(5),Bit#(32)) leftVector <- mkRFileSingleFull;
  method sub = leftVector.sub;
  method upd = leftVector.upd;
endmodule

interface IWorkVectorVer;
  method ActionValue#(Bit#(32)) sub(Bit#(4) addr); 
  method Action upd(Bit#(4) addr, Bit#(32) data);
endinterface
 
(*synthesize*)
module mkWorkVectorVer(IWorkVectorVer);
  RFileSingle#(Bit#(4),Bit#(32)) workVector <- mkRFileSingleFull();
  method sub = workVector.sub;
  method upd = workVector.upd;
endmodule

interface IWorkVectorHor;
  method ActionValue#(Bit#(32)) sub(Bit#(3) addr); 
  method Action upd(Bit#(3) addr, Bit#(32) data);
endinterface
 
(*synthesize*)
module mkWorkVectorHor(IWorkVectorHor);
  RFileSingle#(Bit#(3),Bit#(32)) workVector <- mkRFileSingleFull();
  method sub = workVector.sub;
  method upd = workVector.upd;
endmodule

interface ITopVector;
  method ActionValue#(Bit#(32)) sub(Bit#(4) addr); 
  method Action upd(Bit#(4) addr, Bit#(32) data);  
endinterface
 
(*synthesize*)
module mkTopVector(ITopVector);
  RFileSingle#(Bit#(4),Bit#(32)) topVector <- mkRFileSingleFull();
  method sub = topVector.sub;
  method upd = topVector.upd;
endmodule

interface IbSVector;
  method ActionValue#(Bit#(3)) sub(Bit#(4) addr); 
  method Action upd(Bit#(4) addr, Bit#(3) data);  
endinterface
 
(*synthesize*)
module mkbSVector(IbSVector);
  RFileSingle#(Bit#(4),Bit#(3)) bsVector <- mkRFileSingleFull();
  method sub = bsVector.sub;
  method upd = bsVector.upd;
endmodule





(* synthesize *)
module mkDeblockFilter( IDeblockFilter );

   FIFOF#(EntropyDecOT) infifo     <- mkSizedFIFOF(deblockFilter_infifo_size);
   FIFO#(DeblockFilterOT) outfifo <- mkFIFO();
   FIFO#(DeblockFilterOT) outfifoVertical <- mkSizedFIFO(5);

   FIFO#(MemReq#(TAdd#(PicWidthSz,5),32)) dataMemReqQ       <- mkFIFO;
   FIFO#(MemReq#(TAdd#(PicWidthSz,5),32)) memReqRowToColumnConversion <- mkFIFO();
   FIFO#(MemReq#(TAdd#(PicWidthSz,5),32)) memReqVertical              <- mkFIFO();
   FIFO#(MemReq#(TAdd#(PicWidthSz,5),32)) memReqDataSendReq           <- mkFIFO();

   FIFO#(MemReq#(PicWidthSz,13))          parameterMemReqQ  <- mkFIFO;
   FIFO#(MemResp#(32))                    dataMemRespQ      <- mkFIFO;
   FIFO#(MemResp#(13))                    parameterMemRespQ <- mkFIFO;

   Reg#(Process) process       <- mkReg(Passing);
   Reg#(VerticalState) verticalState <- mkReg(NormalOperation);
   Reg#(Bit#(1)) chromaFlag    <- mkReg(0);
   Reg#(Bit#(5)) dataReqCount  <- mkReg(0);
   Reg#(Bit#(5)) dataRespCount <- mkReg(0);
   Reg#(Bit#(4)) blockNum      <- mkReg(0);
   Reg#(Bit#(2)) pixelNum      <- mkReg(0);

   Reg#(Bool) filterTopMbEdgeFlag     <- mkReg(False);
   Reg#(Bool) filterLeftMbEdgeFlag    <- mkReg(False);
   Reg#(Bool) filterInternalEdgesFlag <- mkReg(False);

   Reg#(Bit#(PicWidthSz))  picWidth  <- mkReg(maxPicWidthInMB);
   Reg#(Bit#(PicHeightSz)) picHeight <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   firstMb   <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   currMb    <- mkReg(0);
   Reg#(Bit#(PicAreaSz))   currMbHor <- mkReg(0);//horizontal position of currMb
   Reg#(Bit#(PicHeightSz)) currMbVer <- mkReg(0);//vertical position of currMb

   Reg#(Bit#(2)) disable_deblocking_filter_idc <- mkReg(0);
   Reg#(Bit#(5)) slice_alpha_c0_offset <- mkReg(0);
   Reg#(Bit#(5)) slice_beta_offset <- mkReg(0);

   Reg#(Bit#(6)) curr_qpy   <- mkReg(0);
   Reg#(Bit#(6)) left_qpy   <- mkReg(0);
   Reg#(Bit#(6)) top_qpy    <- mkReg(0);
   Reg#(Bit#(6)) curr_qpc   <- mkReg(0);
   Reg#(Bit#(6)) left_qpc   <- mkReg(0);
   Reg#(Bit#(6)) top_qpc    <- mkReg(0);
   Reg#(Bit#(1)) curr_intra <- mkReg(0);
   Reg#(Bit#(1)) left_intra <- mkReg(0);
   Reg#(Bit#(1)) top_intra  <- mkReg(0);

   Reg#(Bit#(2)) blockHorVerticalCleanup <- mkReg(0);

   Reg#(Bit#(8)) alphaInternal  <- mkReg(0);
   Reg#(Bit#(5)) betaInternal   <- mkReg(0);
   Reg#(Vector#(3,Bit#(5))) tc0Internal <- mkRegU();   

   Bit#(8) alpha_table[52] = {0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
			      0,  0,  0,  0,  0,  0,  4,  4,  5,  6,
			      7,  8,  9, 10, 12, 13, 15, 17, 20, 22,
			     25, 28, 32, 36, 40, 45, 50, 56, 63, 71,
			     80, 90,101,113,127,144,162,182,203,226,
			    255,255};
   Bit#(5) beta_table[52] = {0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
			     0,  0,  0,  0,  0,  0,  2,  2,  2,  3,
			     3,  3,  3,  4,  4,  4,  6,  6,  7,  7,
			     8,  8,  9,  9, 10, 10, 11, 11, 12, 12,
			    13, 13, 14, 14, 15, 15, 16, 16, 17, 17,
			    18, 18};
   Bit#(5) tc0_table[52][3] = {{ 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 },
			       { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 },
			       { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 },
			       { 0, 0, 1 }, { 0, 0, 1 }, { 0, 0, 1 }, { 0, 1, 1 }, { 0, 1, 1 }, { 1, 1, 1 },
			       { 1, 1, 1 }, { 1, 1, 1 }, { 1, 1, 1 }, { 1, 1, 2 }, { 1, 1, 2 }, { 1, 1, 2 },
			       { 1, 1, 2 }, { 1, 2, 3 }, { 1, 2, 3 }, { 2, 2, 3 }, { 2, 2, 4 }, { 2, 3, 4 },
			       { 2, 3, 4 }, { 3, 3, 5 }, { 3, 4, 6 }, { 3, 4, 6 }, { 4, 5, 7 }, { 4, 5, 8 },
			       { 4, 6, 9 }, { 5, 7,10 }, { 6, 8,11 }, { 6, 8,13 }, { 7,10,14 }, { 8,11,16 },
			       { 9,12,18 }, {10,13,20 }, {11,15,23 }, {13,17,25 }};

   IWorkVectorHor workVectorRows <- mkWorkVectorHor();
   IWorkVectorVer workVectorCols <- mkWorkVectorVer();
   ILeftVector leftVector <- mkLeftVector();
   ITopVector  topVector  <- mkTopVector();
   Reg#(Bit#(16)) topVectorValidBits <- mkReg(0);  

   IbSVector bSfileHor <- mkbSVector();
   IbSVector bSfileVer <- mkbSVector();

   Reg#(Bit#(6)) cleanup_state <- mkReg(0);

   Vector#(4, FIFO#(Bit#(32))) rowToColumnStore <- replicateM(mkSizedFIFO(3));
   Reg#(Bit#(2)) rowToColumnState <- mkReg(0);
   FIFO#(Tuple2#(Bit#(4),Bit#(1))) rowToColumnStoreBlock <- mkFIFO(); // The third bit 1 is to rotate the damned 
                                                                              // last left vector block
   FIFO#(Tuple2#(Bit#(4), Bit#(32))) verticalFilterBlock <- mkFIFO();

   Reg#(Bit#(2)) columnState <- mkReg(0);
   Vector#(4, FIFO#(Bit#(32))) columnToRowStore <- replicateM(mkSizedFIFO(3));
   Reg#(Bit#(2)) columnToRowState <- mkReg(0);
   FIFO#(Tuple2#(Bit#(4), Bit#(1))) columnToRowStoreBlock <- mkFIFO(); 

   Reg#(Bit#(2)) columnNumber <- mkReg(0);      
  
   // Debugging register
   Reg#(Bit#(32)) fifo_full_count <- mkReg(0);
   Reg#(Bit#(32)) fifo_empty_count <- mkReg(0);
   Reg#(Bit#(32)) total_cycles <- mkReg(0);


   rule incr;
     total_cycles <= total_cycles + 1;
   endrule

   rule emptyFIFO;
     if(!infifo.notEmpty)
       begin
          fifo_empty_count <= fifo_empty_count + 1;
          $display("DEBLOCK FIFO EMPTY: %d of %d",fifo_empty_count, total_cycles); 
       end   
   endrule

   rule checkFIFO ( True );
      $display( "Trace DeblockFilter: checkFIFO %h cycle: %d", infifo.first(), total_cycles );
      $display( "TRACE DeblockFilter: checkFIFO %h", infifo.first() );
      if(!infifo.notFull)
        begin
          fifo_full_count <= fifo_full_count + 1;
          $display("DEBLOCK FIFO(%d) FULL: %d of %d",deblockFilter_infifo_size, fifo_full_count, total_cycles); 
        end       
   endrule

   rule memReqMergeRowToColumnConversion;
     memReqRowToColumnConversion.deq();
     dataMemReqQ.enq(memReqRowToColumnConversion.first());
   endrule

   rule memReqMergeVertical;
     memReqVertical.deq();
     dataMemReqQ.enq(memReqVertical.first());
   endrule

   rule memReqMergeDataSendReq;
     memReqDataSendReq.deq();
     dataMemReqQ.enq(memReqDataSendReq.first());
   endrule
 
   rule outfifoVerticalSplit;
     outfifoVertical.deq();
     outfifo.enq(outfifoVertical.first());
   endrule

   rule passing ( process matches Passing );
      case (infifo.first()) matches
	 tagged NewUnit . xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	       $display("ccl5newunit");
	       $display("ccl5rbspbyte %h", xdata);
	    end
	 tagged SPSpic_width_in_mbs .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	       picWidth <= xdata;
	    end
	 tagged SPSpic_height_in_map_units .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	       picHeight <= xdata; 
	    end
	 tagged PPSdeblocking_filter_control_present_flag .xdata :
	    begin
	       infifo.deq();
	       if (xdata == 0)
		  begin
		     disable_deblocking_filter_idc <= 0;
		     slice_alpha_c0_offset <= 0;
		     slice_beta_offset <= 0;
		  end
	    end
	 tagged SHfirst_mb_in_slice .xdata :
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	       firstMb   <= xdata;
	       currMb    <= xdata;
	       currMbHor <= xdata;
	       currMbVer <= 0;
	    end
	 tagged SHdisable_deblocking_filter_idc .xdata :
	    begin
	       infifo.deq();
	       disable_deblocking_filter_idc <= xdata;
	    end
	 tagged SHslice_alpha_c0_offset .xdata :
	    begin
	       infifo.deq();
	       slice_alpha_c0_offset <= xdata;
	    end
	 tagged SHslice_beta_offset .xdata :
	    begin
	       infifo.deq();
	       slice_beta_offset <= xdata;
	    end
	 tagged IBTmb_qp .xdata :
	    begin
	       infifo.deq();
	       curr_qpy <= xdata.qpy;
	       curr_qpc <= xdata.qpc;
	    end
	 tagged PBbS .xdata :
	    begin
	       process <= Initialize;
	    end
	 tagged PBoutput .xdata :
	    begin
	       $display( "ERROR Deblocking Filter: passing PBoutput");
	    end
	 tagged EndOfFile :
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	       $display( "ccl5: EndOfFile reached");
	       //$finish(0);
	    end
	 default:
	    begin
	       infifo.deq();
	       outfifo.enq(EDOT (infifo.first()));
	    end
      endcase
   endrule

   // What does this rule do?
   rule currMbHorUpdate( !(currMbHor<zeroExtend(picWidth)) );
      $display( "TRACE Deblocking Filter: strange update rule firing... %0d", currMb); 
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
   endrule

   
   rule initialize ( process==Initialize && currMbHor<zeroExtend(picWidth) );
      $display( "TRACE Deblocking Filter: initialize %0d", currMb);
      process <= Horizontal;
      dataReqCount <= 1;
      dataRespCount <= 1;
      filterTopMbEdgeFlag <= !(currMb<zeroExtend(picWidth) || disable_deblocking_filter_idc==1 || (disable_deblocking_filter_idc==2 && currMb-firstMb<zeroExtend(picWidth)));
      filterLeftMbEdgeFlag <= !(currMbHor==0 || disable_deblocking_filter_idc==1 || (disable_deblocking_filter_idc==2 && currMb==firstMb));
      filterInternalEdgesFlag <= !(disable_deblocking_filter_idc==1);
      blockNum <= 0;
      pixelNum <= 0;
      topVectorValidBits <= 0;
   endrule 

   rule dataSendReq ( dataReqCount>0 && currMbHor<zeroExtend(picWidth) );
      $display( "TRACE Deblocking Filter: dataSendReq %0d", dataReqCount);
      Bit#(PicWidthSz) temp = truncate(currMbHor);
      if(currMb<zeroExtend(picWidth))
	 dataReqCount <= 0;
      else
	 begin
	    if(dataReqCount==1)
	       parameterMemReqQ.enq(LoadReq (temp));
	    Bit#(4) temp2 = truncate(dataReqCount-1);
	    let temp3 = {temp,chromaFlag,temp2};
            memReqDataSendReq.enq(LoadReq (temp3));
	    if(dataReqCount==16)
	       dataReqCount <= 0;
	    else
	       dataReqCount <= dataReqCount+1;
	 end
   endrule


   rule dataReceiveNoResp ( dataRespCount>0 && currMb<zeroExtend(picWidth) && currMb-firstMb<zeroExtend(picWidth) );
      $display( "TRACE Deblocking Filter: dataReceiveNoResp");
      dataRespCount <= 0;
   endrule

   function Action deque(FIFO#(Bit#(32)) fifo);
     return fifo.deq();
   endfunction

   // rotate column to row major after applying the horizontal filter
   rule rowToColumnConversion;      
     // Check to see if we're even filtering the top edge
     Bit#(2) blockVer = {tpl_1(rowToColumnStoreBlock.first())[3],tpl_1(rowToColumnStoreBlock.first())[1]};
     Bit#(2) blockHor = {tpl_1(rowToColumnStoreBlock.first())[2],tpl_1(rowToColumnStoreBlock.first())[0]};
     Bool storeBottomRightBlock = tpl_2(rowToColumnStoreBlock.first()) == 1;

     rowToColumnState  <= rowToColumnState + 1;
     Bit#(32) data_out = 0;
     Bit#(PicWidthSz) adjustedMbHor = ((currMbHor==0) ? (picWidth-1) : truncate(currMbHor-1));
                 
     case(rowToColumnState) 
       2'b00: data_out = {(rowToColumnStore[3].first())[7:0], (rowToColumnStore[2].first())[7:0],
                          (rowToColumnStore[1].first())[7:0], (rowToColumnStore[0].first())[7:0]};
           
       2'b01: data_out = {(rowToColumnStore[3].first())[15:8], (rowToColumnStore[2].first())[15:8],
                          (rowToColumnStore[1].first())[15:8], (rowToColumnStore[0].first())[15:8]};

       2'b10: data_out = {(rowToColumnStore[3].first())[23:16], (rowToColumnStore[2].first())[23:16],
                          (rowToColumnStore[1].first())[23:16], (rowToColumnStore[0].first())[23:16]};

       2'b11: begin
                data_out = {(rowToColumnStore[3].first())[31:24], (rowToColumnStore[2].first())[31:24],
                            (rowToColumnStore[1].first())[31:24], (rowToColumnStore[0].first())[31:24]};
                mapM_(deque, rowToColumnStore); // Deq the vector elements
                rowToColumnStoreBlock.deq();
             end
       endcase

     if(storeBottomRightBlock) // The right bottom block is not complete until the top filtering has occured 
                               // It has to be rotated to the column major ordering used in the top vector 
                               // memory
       begin
          $display( "TRACE Deblocking Filter: rowToColumnRotate rotating block (%0d, %0d) rowtoColumnState: %d bottomRightBlock: %d, data: %h", blockHor, blockVer, rowToColumnState, storeBottomRightBlock, data_out);
         // The block hor calculation may be questionable... between U and V.
         if(chromaFlag == 0)
           begin
             memReqRowToColumnConversion.enq(StoreReq {addr:{adjustedMbHor,chromaFlag,2'b11,rowToColumnState},data:data_out});
           end
         else
           begin  //differentiate between u and v
             memReqRowToColumnConversion.enq(StoreReq {addr:{adjustedMbHor,chromaFlag,blockHor[1],1'b1,rowToColumnState},data:data_out});
           end
               
       end
     else // pass data along to vertical filter
       begin  
         verticalFilterBlock.enq(tuple2(tpl_1(rowToColumnStoreBlock.first()),data_out));

         $display( "TRACE Deblocking Filter: rowToColumnRotate rotating block (%0d, %0d) rowtoColumnState: %d bottomRightBlock: %d, data: %h", blockHor, blockVer, rowToColumnState, storeBottomRightBlock, data_out);
       end
   endrule

   // rotate row to column after applying the vertical filter
   rule columnToRowConversion;
     Bit#(32) data_out = 0;
     Bool topValues = tpl_2(columnToRowStoreBlock.first()) == 1;
     Bit#(4) blockNumCols = tpl_1(columnToRowStoreBlock.first());
     Bit#(2) blockHor = {blockNumCols[2],blockNumCols[0]};
     Bit#(2) blockVer = {blockNumCols[3],blockNumCols[1]} - 1; // Subtract 1, because these output values lag slightly  
     columnToRowState  <= columnToRowState + 1;  
                           
     case(columnToRowState)  // not to sure about this ordering
       2'b00: data_out = {(columnToRowStore[3].first())[7:0],
                          (columnToRowStore[2].first())[7:0],
                          (columnToRowStore[1].first())[7:0],
                          (columnToRowStore[0].first())[7:0]};
                                                  
       2'b01: data_out = {(columnToRowStore[3].first())[15:8],
                          (columnToRowStore[2].first())[15:8],
                          (columnToRowStore[1].first())[15:8],
                          (columnToRowStore[0].first())[15:8]};
       2'b10: data_out = {(columnToRowStore[3].first())[23:16],
                          (columnToRowStore[2].first())[23:16],
                          (columnToRowStore[1].first())[23:16],
                          (columnToRowStore[0].first())[23:16]};
       2'b11: begin
                data_out = {(columnToRowStore[3].first())[31:24],
                            (columnToRowStore[2].first())[31:24],
                            (columnToRowStore[1].first())[31:24],
                            (columnToRowStore[0].first())[31:24]};                                             
                mapM_(deque, columnToRowStore); // Deq the vector elements               
                columnToRowStoreBlock.deq();
              end
     endcase     
     $write( "TRACE Deblocking Filter: columnToRow rotate block(%0d, %0d) columnToRowState %d, topValues: %d, data: %h", blockHor, blockVer, columnToRowState, topValues, data_out);

     Bit#(PicWidthSz) currMbHorT = truncate(currMbHor);
     // Actually send the data out. This stuff is not the bottom row or left column, and is therefore done.
     // THe bottom row was sent out to the temporary buffer in the vertical rule.  But if we're on the last row of
     // the frame, there coming here.  Also, if we're in the last block, we must output the leftvector values
     if( !topValues && (!(blockHor==3 || (blockHor[0]==1 && chromaFlag==1)) || (currMbVer==picHeight-1)))
       begin       
         $display( " Normal");
         if(chromaFlag==0)
           begin
             $display("TRACE mkDeblockFilter: Outputting Luma ver{mbVer, blockVer(2), state}: %h, hor{mbHor, blockHor(2)}: %b, data: %h", {currMbVer,blockVer}, {currMbHorT,blockHor}, data_out); 
             outfifo.enq(DFBLuma {ver:{currMbVer,blockVer,columnToRowState},
                                  hor:{currMbHorT,blockHor},
                                  data:data_out});
           end
         else
           begin
 $display("TRACE mkDeblockFilter: Outputting Chroma %d ver{mbVer, blockVer(1), state(2)}: %b, hor{mbHor, blockHor(1)}: %b, data: %h",blockHor[1],{currMbVer,blockVer[0],columnToRowState},{currMbHorT,blockHor[0]},data_out); 
             outfifo.enq(DFBChroma {uv:blockHor[1],
                                    ver:{currMbVer,blockVer[0],columnToRowState},
                                    hor:{currMbHorT,blockHor[0]},
                                    data:data_out});
           end
       end

     if(topValues)// These are the previous top values, and they must be sent out.  Note, that since this is a past
                       // Mb, we must adjust the the Mbs used.   
       begin   
         $display( " TopValues");              
         if(chromaFlag==0)
           begin 
             $display("TRACE mkDeblockFilter: (Top Value) Outputting Luma ver{mbVer, blockVer(2), state(2)}: %b, hor{mbHor, blockHor(2)}: %h, data: %h",{currMbVer-1,2'b11,columnToRowState}, {currMbHorT,blockHor}, data_out); 
             outfifo.enq(DFBLuma {ver:{currMbVer-1,2'b11,columnToRowState},
                                  hor:{currMbHorT,blockHor},
                                  data:data_out});
           end
         else
           begin                
             $display("TRACE mkDeblockFilter: (Top Value) Outputting Chroma %d ver{mbVer, blockVer(1), state(2)}: %b, hor{mbHor, blockHor(1)}: %b, data: %h",blockHor[1],{currMbVer-1,1'b1,columnToRowState},{currMbHorT,blockHor[0]},data_out);              
             outfifo.enq(DFBChroma {uv:blockHor[1],
                                    ver:{currMbVer-1,1'b1,columnToRowState},
                                    hor:{currMbHorT,blockHor[0]},
                                    data:data_out});
	   end 
       end        

     if( !topValues && (blockHor==3 || (blockHor[0]==1 && chromaFlag==1))) // We need to write to the left Vector which will be used in the future. These values will not be written out.
          // It may be wise at some point to 
       begin
         // We need to check for the last point in the pipeline. This is the bottom right corner of the Mb.
         $display( " Left Vector");
	 if(chromaFlag==0)
           begin
             if((blockVer == 3) && (columnToRowState == 3))
               begin
                 process <= Cleanup;
               end
             //check for last macro block         
	     leftVector.upd({1'b0,blockVer,columnToRowState}, data_out);
           end
	 else
	   begin
             // Only cleanup a single time after the chroma blocks
             if((blockHor == 3) && (blockVer[0] == 1) && (columnToRowState == 3))
               begin
                 process <= Cleanup;
               end
             leftVector.upd({1'b1,blockHor[1],blockVer[0],columnToRowState}, data_out);
           end     
	 end
 
   endrule

   
   rule dataReceiveResp ( dataRespCount>0 && !(currMb<zeroExtend(picWidth)) && currMbHor<zeroExtend(picWidth) );
      $display( "TRACE Deblocking Filter: dataReceiveResp %0d", dataRespCount);
      Bit#(4) temp = truncate(dataRespCount-1);
      if(dataRespCount==1)
	 begin
	    Bit#(13) tempParameters=0;
	    if(parameterMemRespQ.first() matches tagged LoadResp .xdata)
	       tempParameters = xdata;
	    top_qpy <= tempParameters[5:0];
	    top_qpc <= tempParameters[11:6];
	    top_intra <= tempParameters[12];
	    parameterMemRespQ.deq();
	 end
      if(dataRespCount==16)
	 dataRespCount <= 0;
      else
	 dataRespCount <= dataRespCount+1;
      if(dataMemRespQ.first() matches tagged LoadResp .xdata)
        begin
          topVectorValidBits[temp] <= 1;
	  topVector.upd(temp, xdata);
        end
      dataMemRespQ.deq();
      //$display( "TRACE Deblocking Filter: dataReceiveResp topVector %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h", topVector[0], topVector[1], topVector[2], topVector[3], topVector[4], topVector[5], topVector[6], topVector[7], topVector[8], topVector[9], topVector[10], topVector[11], topVector[12], topVector[13], topVector[14], topVector[15]);
   endrule


   rule horizontal ( process==Horizontal && currMbHor<zeroExtend(picWidth) );
      Bit#(2) blockHor = {blockNum[2],blockNum[0]};
      Bit#(2) blockVer = {blockNum[3],blockNum[1]};
      Bit#(2) pixelVer = pixelNum;

      Bool leftEdge = (blockNum[0]==0 && (blockNum[2]==0 || chromaFlag==1));
      if(blockNum==0 && pixelNum==0)
	 begin
	    Bit#(6) qpav = (chromaFlag==0 ? curr_qpy : curr_qpc);
	    Bit#(8) indexAtemp = zeroExtend(qpav)+signExtend(slice_alpha_c0_offset);
	    Bit#(8) indexBtemp = zeroExtend(qpav)+signExtend(slice_beta_offset);
	    Bit#(6) indexA = (indexAtemp[7]==1 ? 0 : (indexAtemp[6:0]>51 ? 51 : indexAtemp[5:0]));
	    Bit#(6) indexB = (indexBtemp[7]==1 ? 0 : (indexBtemp[6:0]>51 ? 51 : indexBtemp[5:0]));
	    alphaInternal <= alpha_table[indexA];
	    betaInternal <= beta_table[indexB];
	    Vector#(3,Bit#(5)) tc0temp = arrayToVector(tc0_table[indexA]);
	    tc0Internal <= tc0temp;
	 end
      case (infifo.first()) matches
	 tagged PBbS .xdata :
	    begin
	       infifo.deq();	       
               bSfileHor.upd(blockNum, xdata.bShor);
               bSfileVer.upd(blockNum, xdata.bSver);
               $display( "TRACE Deblocking Filter: horizontal bsFIFO data: %d, subblock(%0d, %0d) row: %0d, ",infifo.first(), blockHor, blockVer, pixelNum);
	    end
	 tagged PBoutput .xdata :
	    begin
               Bit#(PicWidthSz) currMbHorT = truncate(currMbHor);
               if((chromaFlag == 1) && (blockHor[1] == 1))
                 begin
                   $display("PRE %h %h %h", {currMbVer,blockVer[0],pixelVer},{currMbHorT,blockHor[0]}, {xdata[0],xdata[1],xdata[2],xdata[3]});
                 end
               $display( "TRACE Deblocking Filter: horizontal chroma: %d, subblock(%0d, %0d) row: %0d, data: %h", chromaFlag, blockHor, blockVer, pixelNum, xdata);
	       infifo.deq();
	       Bit#(6) addrq = {blockHor,blockVer,pixelVer};
	       Bit#(5) addrpLeft = (chromaFlag==0 ? {1'b0,blockVer,pixelVer} : {1'b1,blockHor[1],blockVer[0],pixelVer});
	       Bit#(6) addrpCurr = {(blockHor-1),blockVer,pixelVer};
	       Bit#(32) pixelq = {xdata[3],xdata[2],xdata[1],xdata[0]};
	       Bit#(32) pixelp;
	       if(leftEdge)
                 begin
		   pixelp <- leftVector.sub(addrpLeft);
                   $display( "TRACE Deblocking Filter: horizontal P (left) addr %h, data %h ",addrpLeft, pixelp);
                 end
	       else
                 begin
                   pixelp <- workVectorRows.sub({blockVer[0], pixelVer});
                   $display( "TRACE Deblocking Filter: horizontal P (work) addr %h, data %h ",addrpCurr, pixelp);
                 end
	       Bit#(64) result = {pixelq,pixelp};
	       if(leftEdge && filterLeftMbEdgeFlag)
		  begin
                    Bit#(6) curr_qp = (chromaFlag==0 ? curr_qpy : curr_qpc);
                    Bit#(6) left_qp = (chromaFlag==0 ? left_qpy : left_qpc);
                    Bit#(7) qpavtemp = zeroExtend(curr_qp)+zeroExtend(left_qp)+1;
                    Bit#(6) qpav = qpavtemp[6:1];
                    Bit#(8) indexAtemp = zeroExtend(qpav)+signExtend(slice_alpha_c0_offset);
                    Bit#(8) indexBtemp = zeroExtend(qpav)+signExtend(slice_beta_offset);
                    Bit#(6) indexA = (indexAtemp[7]==1 ? 0 : (indexAtemp[6:0]>51 ? 51 : indexAtemp[5:0]));
                    Bit#(6) indexB = (indexBtemp[7]==1 ? 0 : (indexBtemp[6:0]>51 ? 51 : indexBtemp[5:0]));
                    Bit#(8) alphaMbLeft = alpha_table[indexA];
                    Bit#(5) betaMbLeft = beta_table[indexB];
                    Vector#(3,Bit#(5)) tc0MbLeft = arrayToVector(tc0_table[indexA]);
		    if(filter_test({pixelq[15:0],pixelp[31:16]},alphaMbLeft,betaMbLeft))
                      begin
                         $display("TRACE mkDeblockFilter: Applying horizontal, left filter");
                         Bit#(3) bsData <- bSfileHor.sub((chromaFlag==0?blockNum:{blockNum[1:0],pixelVer[1],1'b0}));
                         result = filter_input({pixelq,pixelp},chromaFlag==1,bsData,alphaMbLeft,betaMbLeft,tc0MbLeft);
                       end
		  end
	       else if(!leftEdge && filterInternalEdgesFlag)
		  begin
		     if(filter_test({pixelq[15:0],pixelp[31:16]},alphaInternal,betaInternal))
                       begin
                         $display("TRACE mkDeblockFilter: Applying horizontal, internal filter");
                         Bit#(3) bSData <- bSfileHor.sub((chromaFlag==0?blockNum:{blockNum[1:0],pixelVer[1],1'b0})); 
                         result = filter_input({pixelq,pixelp},chromaFlag==1,bSData,alphaInternal,betaInternal,tc0Internal);
                       end
		  end
             

	       if(leftEdge)
                 begin
                   // write out the left edge
                   //Check to store this value to the memory.  I think the rotation is off here.
                   // I should also adjust the vertical Mb...  Figure out MbHorT
               
                   Bit#(PicHeightSz) adjustedMbVer = ((currMbHorT==0) && (currMbVer!=0)) ? currMbVer-1 : currMbVer;
                   Bit#(PicWidthSz)  adjustedMbHor = currMbHorT==0 ? picWidth-1 : currMbHorT-1;
                   // In this case we buffer the bottom vertical element, since it has to be used again
                   if(((blockVer == 3) || ((chromaFlag == 1) && (blockVer == 1))) && (adjustedMbVer != picHeight - 1))
                     begin                      
		       rowToColumnStore[pixelNum[1:0]].enq(result[31:0]);
                       // only push in a command for the bottom leftblock.  It has to be rotated.
                       if(pixelNum == 3)
                         begin
                           rowToColumnStoreBlock.enq(tuple2(blockNum,1));
                         end
                    end
                   // these outputs occur in the past, so we must use the adjusted Mb numbers 
                   else if(chromaFlag==0)
                     begin
                       $display("TRACE mkDeblockFilter: (Left Vector) Outputting Luma ver{mbVer, blockVer(2), state(2)}: %b, hor{mbHor, blockHor(2)}: %b, data: %h",{adjustedMbVer,blockVer,pixelNum},{adjustedMbHor,2'b11} ,result[31:0] ); 
                       outfifoVertical.enq(DFBLuma {ver:{adjustedMbVer,blockVer,pixelVer},
                                            hor:{adjustedMbHor,2'b11},
                                            data:result[31:0]});
                     end
                   else
                     begin
                       $display("TRACE mkDeblockFilter: (Left Vector) Outputting Chroma %d ver{mbVer, blockVer(2), state(2)}: %b, hor{mbHor, blockHor(2)}: %b, data: %h",blockHor[1],{adjustedMbVer,blockVer[0],pixelNum},{adjustedMbHor,1'b1}  ,result[31:0]);
                       outfifoVertical.enq(DFBChroma {uv:blockHor[1],
                                              ver:{adjustedMbVer,blockVer[0],pixelVer},
                                              hor:{adjustedMbHor,1'b1},
                                              data:result[31:0]});
                      end                                 
               	 end	  
	       else
                  begin
                    // push the correction into reorder block;
                    rowToColumnStore[addrpCurr[1:0]].enq(result[31:0]);                             
                    // Push down the block number and the chroma flag into the pipeline
                    if(pixelNum == 3)
                      begin
                        let blockHorPast = blockHor - 1;
                        let blockNumPast = {blockVer[1], blockHorPast[1], blockVer[0], blockHorPast[0]};
                        rowToColumnStoreBlock.enq(tuple2(blockNumPast,0));                   
                      end
                  end
               $display( "TRACE Deblocking Filter: horizontal Q (work) addr %h, data %h, original data: %h ",addrq, result[63:32], pixelq);
               workVectorRows.upd({blockVer[0],pixelVer}, result[63:32]);
	 
               // Step out to clean up the edge block
               // What about the chroma?  
               if((pixelNum == 3) && ((blockHor == 3) || ((chromaFlag == 1) && (blockHor == 1)))) 
                 begin
                    $display( "TRACE Deblocking Filter: Heading to Horizontal Cleanup"); 
                   process <= HorizontalCleanup;// we enter this state to push out the remaining
                                                  // blocks, that haven't been shoved out.  Namely, the
                                                  // left blocks.
                 end
	       else if(pixelNum==3)
                 begin
                   $display( "TRACE Deblocking Filter: horizontal bsFIFO completed subblock(%0d, %0d)", blockHor, blockVer);
		   blockNum <= blockNum+1;
                 end              
	       pixelNum <= pixelNum+1;
	    end
	 default: $display( "ERROR Deblocking Filter: horizontal non-PBoutput input");
      endcase
   endrule

  rule horizontal_cleanup(process == HorizontalCleanup);
    Bit#(2) blockHor = {blockNum[2],blockNum[0]};
    Bit#(2) blockVer = {blockNum[3],blockNum[1]};
    $display( "TRACE Deblocking Filter: horizontal_cleanup (%0d, %0d) row: %d", blockHor, blockVer, pixelNum);
    if(pixelNum==3 && (blockNum==15 || (blockNum==7 && chromaFlag==1)))
      begin
        if(blockNum == 15)
          begin
            $display( "TRACE Deblocking Filter: horizontal completed Mb (%0d) Luma", currMb);
          end
        else
          begin
            $display( "TRACE Deblocking Filter: horizontal completed Mb (%0d) Chroma", currMb);
          end
        blockNum <= 0;
        process <= Vertical;// we enter this state to wait for the vertical processing to complete
        rowToColumnStoreBlock.enq(tuple2(blockNum,0));
      end
    else if(pixelNum == 3)
      begin        
        blockNum <= blockNum + 1;
        process <= Horizontal; // not done with this Mb yet.
        rowToColumnStoreBlock.enq(tuple2(blockNum,0));
      end
    pixelNum <= pixelNum + 1;
    // push the correction into reorder block;
    Bit#(32) work_data <- workVectorRows.sub({blockVer[0], pixelNum});
    rowToColumnStore[pixelNum].enq(work_data);
  endrule


  // declare these to share the rule
  begin 
   Bit#(4) blockNumCols = tpl_1(verticalFilterBlock.first());
   Bit#(2) blockVer = {blockNumCols[3],blockNumCols[1]};    
   Bit#(2) blockHor = {blockNumCols[2],blockNumCols[0]};
   Bool topEdge = (blockVer==0);
  

  rule vertical_filter_halt((verticalState == NormalOperation) && !((!topEdge) || (topVectorValidBits[{blockHor,columnNumber}] == 1) || (currMb<zeroExtend(picWidth))));
        if(process == Vertical || process == Horizontal)
          begin
            $display("TRACE Deblocking Filter: Vertical processing halted on block: %h (%0d, %0d), column %d chromaFlag %d due to data dependency",  blockNumCols, blockHor, blockVer, columnNumber, chromaFlag);
          end

  endrule


  // As with horizontal, the q data will be read from the data store, and the p data will be streamed in via the
  // reordering FIFO.  The new p data must be stored, but the q data will need to be spooled out, since it needs to 
  // make it to the left vector.
  rule vertical((verticalState == NormalOperation) && ((!topEdge) || (topVectorValidBits[{blockHor,columnNumber}] == 1) || (currMb<zeroExtend(picWidth))));
    //$display( "TRACE Deblocking Filter: vertical %0d %0d", colNum, rowNum);
    //$display( "TRACE Deblocking Filter: vertical topVector %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h %h", topVector[0], topVector[1], topVector[2], topVector[3], topVector[4], topVector[5], topVector[6], topVector[7], topVector[8], topVector[9], topVector[10], topVector[11], topVector[12], topVector[13], topVector[14], topVector[15]);
    //Process the block according to what got passed to us.
    Bit#(32) workV = tpl_2(verticalFilterBlock.first()); 
    Bit#(32) tempV = 0;
    Bit#(64) resultV = 0;
    Bit#(8) alpha;
    Bit#(5) beta;
    Vector#(3,Bit#(5)) tc0;


      $display( "TRACE Deblocking Filter: vertical subblock (%0d, %0d), column: %d, data: %h", blockHor, blockVer, columnNumber, workV);
      columnNumber <= columnNumber + 1;
      verticalFilterBlock.deq();
      if(topEdge)
	 begin
            Bit#(6) curr_qp = (chromaFlag==0 ? curr_qpy : curr_qpc);
	    Bit#(6) top_qp = (chromaFlag==0 ? top_qpy : top_qpc);
	    Bit#(7) qpavtemp = zeroExtend(curr_qp)+zeroExtend(top_qp)+1;
	    Bit#(6) qpav = qpavtemp[6:1];
	    Bit#(8) indexAtemp = zeroExtend(qpav)+signExtend(slice_alpha_c0_offset);
	    Bit#(8) indexBtemp = zeroExtend(qpav)+signExtend(slice_beta_offset);
	    Bit#(6) indexA = (indexAtemp[7]==1 ? 0 : (indexAtemp[6:0]>51 ? 51 : indexAtemp[5:0]));
	    Bit#(6) indexB = (indexBtemp[7]==1 ? 0 : (indexBtemp[6:0]>51 ? 51 : indexBtemp[5:0]));
	    Bit#(8) alphaMbTop = alpha_table[indexA];
	    Bit#(5) betaMbTop = beta_table[indexB];
	    Vector#(3,Bit#(5)) tc0MbTop = arrayToVector(tc0_table[indexA]);
	    tempV <- topVector.sub({blockHor,columnNumber});
            $display( "TRACE Deblocking Filter: vertical P (top) addr %h, orig data %h ",{blockVer,columnNumber}, tempV);
	    alpha = alphaMbTop;
	    beta = betaMbTop;
	    tc0 = tc0MbTop;
	 end
      else
	 begin  
            // We read this value from the original vector           
	    tempV <- topVector.sub({blockHor, columnNumber});	
            $display( "TRACE Deblocking Filter: vertical P (work) addr %h, orig data %h ",{blockHor, blockVer - 1, columnNumber}, tempV);   
	    alpha = alphaInternal;
	    beta = betaInternal;
	    tc0 = tc0Internal;
	 end

      // Marshalling data in things upon which the filter blocks can be applied

      resultV = {tpl_2(verticalFilterBlock.first()),tempV};

      // Apply filter, only if filter test passes, and we are either filtering the top edge, or we aren't on the top edge
      $display( "TRACE Deblocking Filter: vertical Filter test: P1P0Q0Q1: %h",{workV[15:8],workV[7:0],tempV[31:24],tempV[23:16]}); 
      if((filter_test({workV[15:8],workV[7:0],tempV[31:24],tempV[23:16]},alpha,beta)) && ((topEdge && filterTopMbEdgeFlag)|| (!topEdge && filterInternalEdgesFlag) ))
        begin
          $display("TRACE mkDeblockFilter: Applying vertical filter");
          Bit#(3) bsData <- bSfileVer.sub((chromaFlag==0?blockNumCols:{blockVer[0],blockHor[0],1'b0,columnNumber[1]}));
	  resultV = filter_input(resultV,chromaFlag==1,bsData,alpha,beta,tc0);
        end
      //Write out the result data  31:0 are the done q values
      if(topEdge)
	 begin
            // We really need to just output these values -> need to shove them to the rotation unit, but only if the 
            // current Mb vertical component is larger than 0.  All of these are done and can be dumped out
            if(currMbVer > 0)
              begin
                if(columnNumber == 3)
                  begin
                    columnToRowStoreBlock.enq(tuple2(blockNumCols,1'b1));
                  end
                columnToRowStore[columnNumber].enq(resultV[31:0]);
              end
	 end
      else
	 begin
            // We should make the decision as to whether to store these values. We will store the bottom row, except
            // for the left most block which will be stored the next time that an Mb gets processed.
            // The values to store are in the P vector... except the bottom right block, which is different.
            Bit#(PicWidthSz) currMbHorT = truncate(currMbHor);   
            
            if(((blockVer == 3) && (blockHor == 3)) || ((chromaFlag == 1) && (blockVer == 1) && (blockHor[0] == 1)))
              begin
                // need to enter escape state to write the bottom left block to the leftVector. 
                if(columnNumber == 3)
                  begin
                    blockHorVerticalCleanup <= blockHor;
                    verticalState <= VerticalCleanup;
                  end                
              end  
            else if((blockVer == 3) || ((chromaFlag == 1) && (blockVer == 1)))
              begin
                if((currMbVer == picHeight - 1) && (columnNumber == 3)) // If we're at the bottom of the frame, we'd 
                                                                        // roll through the block clean up.
                  begin
                    blockHorVerticalCleanup <= blockHor;
                    verticalState <= VerticalCleanup;
                  end                 
                memReqVertical.enq(StoreReq {addr:{currMbHorT,chromaFlag,blockHor,columnNumber},data:resultV[63:32]});
              end
            columnToRowStore[columnNumber].enq(resultV[31:0]);
            if(columnNumber == 0)
              begin
                columnToRowStoreBlock.enq(tuple2(blockNumCols,1'b0));
              end            
	 end

        $display( "TRACE Deblocking Filter: vertical P                 data %h                     ",  resultV[31:0]); 
        $display( "TRACE Deblocking Filter: vertical Q (work) addr %h, data %h, original data: %h  ",{blockHor,blockVer,columnNumber}, resultV[63:32], workV);

        topVector.upd({blockHor,columnNumber}, resultV[63:32]);            
  endrule
end

  rule vertical_cleanup(verticalState == VerticalCleanup);
    $display( "TRACE Deblocking Filter: vertical_cleanup at block end column: %d ", columnNumber);
    columnNumber <= columnNumber + 1; 
    if(columnNumber == 3) 
      begin
        verticalState <= NormalOperation;
      end
    if(chromaFlag == 0)
      begin
        Bit#(2) blockHor = blockHorVerticalCleanup;
        Bit#(2) blockVer = 0;
        if(columnNumber == 3)
          begin
            // Horizontal Postion is 3, but vertical position is 0, owing to subtraction in the rotation unit
            columnToRowStoreBlock.enq(tuple2({blockVer[1],blockHor[1],blockVer[0],blockHor[0]},1'b0));
          end      
        Bit#(32) w_data <- topVector.sub({blockHor, columnNumber}); 
        columnToRowStore[columnNumber].enq(w_data);     
     end
   else
     begin        
       Bit#(2) blockHor = blockHorVerticalCleanup;
       Bit#(2) blockVer = 2; // need to make this two for subtraction in rotation unit          
       if(columnNumber == 3)
         begin
           // Horizontal Postion is 3, but vertical position is 0, owing to subtraction in the rotation unit
           columnToRowStoreBlock.enq(tuple2({blockVer[1],blockHor[1],blockVer[0],blockHor[0]},1'b0));
         end          
       Bit#(32) w_data <- topVector.sub({blockHor, columnNumber}); 
       columnToRowStore[columnNumber].enq(w_data);                 
     end
  endrule


  rule cleanup ( process==Cleanup && currMbHor<zeroExtend(picWidth) );
    $display( "TRACE Deblocking Filter: cleanup %0d", currMb);
    Bit#(PicWidthSz) currMbHorT = truncate(currMbHor);     
    if(chromaFlag==0)
      begin		    
        chromaFlag <= 1;
        process <= Initialize;
        $display( "TRACE Deblocking Filter: horizontal bsFIFO luma completed");
      end
    else
      begin
        $display( "TRACE Deblocking Filter: horizontal bsFIFO chroma completed");
        chromaFlag <= 0;
        process <= Passing;
        Bit#(PicWidthSz) temp = truncate(currMbHor);
        parameterMemReqQ.enq(StoreReq {addr:temp,data:{curr_intra,curr_qpc,curr_qpy}});
        left_intra <= curr_intra;
        left_qpc <= curr_qpc;
        left_qpy <= curr_qpy;
        currMb <= currMb+1;
        currMbHor <= currMbHor+1;
        if(currMbVer==picHeight-1 && currMbHor==zeroExtend(picWidth-1))
          begin
            outfifo.enq(EndOfFrame);
          end
      end 	 	     
   endrule
  
   interface Client mem_client_data;
      interface Get request  = fifoToGet(dataMemReqQ);
      interface Put response = fifoToPut(dataMemRespQ);
   endinterface

   interface Client mem_client_parameter;
      interface Get request  = fifoToGet(parameterMemReqQ);
      interface Put response = fifoToPut(parameterMemRespQ);
   endinterface

   interface Put ioin  = fifoToPut(fifofToFifo(infifo));
   interface Get ioout = fifoToGet(outfifo);
      
endmodule

endpackage
