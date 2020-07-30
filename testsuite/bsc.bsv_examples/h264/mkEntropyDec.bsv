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
// Entropy Decoder implementation
//----------------------------------------------------------------------
//
//

package mkEntropyDec;

import H264Types::*;
import ExpGolomb::*;
import CAVLC::*;
import ICalc_nC::*;
import mkCalc_nC::*;
import IEntropyDec::*;
import FIFO::*;

import Connectable::*;
import GetPut::*;
import ClientServer::*;


//-----------------------------------------------------------
// Local Datatypes
//-----------------------------------------------------------

typedef union tagged                
{
 void     Start;            //special state that initializes the process.
 void     NewUnit;          //special state that checks the NAL unit type.
		 
 Bit#(5)  CodedSlice;       //decodes a type of NAL unit
 void     SEI;              //decodes a type of NAL unit
 Bit#(5)  SPS;              //decodes a type of NAL unit
 Bit#(5)  PPS;              //decodes a type of NAL unit
 void     AUD;              //decodes a type of NAL unit
 void     EndSequence;      //decodes a type of NAL unit
 void     EndStream;        //decodes a type of NAL unit
 void     Filler;           //decodes a type of NAL unit

 Bit#(5)  SliceData;        //decodes slice data (part of a CodedSlice NAL unit)
 Bit#(5)  MacroblockLayer;  //decodes macroblock layer (part of a CodedSlice NAL unit)
 Bit#(5)  MbPrediction;     //decodes macroblock prediction (part of a CodedSlice NAL unit)
 Bit#(5)  SubMbPrediction;  //decodes sub-macroblock prediction (part of a CodedSlice NAL unit)
 Bit#(5)  ResidualBlock;    //decodes residual block (part of a CodedSlice NAL unit)
}
State deriving(Eq,Bits);


      
//-----------------------------------------------------------
// Helper functions   
function MbType mbtype_convert( Bit#(5) in_mb_type, Bit#(4) in_slice_type );//converts mb_type syntax element to MbType type
   Bit#(5) tempmb = in_mb_type;
   if(in_slice_type == 2 || in_slice_type == 7)//I slice
      tempmb = in_mb_type+5;
   case ( tempmb )
      0: return P_L0_16x16;
      1: return P_L0_L0_16x8;
      2: return P_L0_L0_8x16;
      3: return P_8x8;
      4: return P_8x8ref0;
      5: return I_NxN;
      30: return I_PCM;
      default:
      begin
	 Bit#(5) tempmb16x16 = tempmb-6;
	 Bit#(2) tempv1 = tempmb16x16[1:0];
	 Bit#(2) tempv2;
	 Bit#(1) tempv3;
	 if(tempmb16x16 < 12)
	    begin
	       tempv3 = 0;
	       tempv2 = tempmb16x16[3:2];
	    end
	 else
	    begin
	       tempv3 = 1;
	       tempv2 = tempmb16x16[3:2]+1;
	    end
	 return I_16x16{intra16x16PredMode:tempv1, codedBlockPatternChroma:tempv2, codedBlockPatternLuma:tempv3};
      end
   endcase
endfunction



//-----------------------------------------------------------
// Entropy Decoder Module
//-----------------------------------------------------------


(* synthesize *)
module mkEntropyDec( IEntropyDec );
   
   FIFO#(NalUnwrapOT)       infifo      <- mkSizedFIFO(entropyDec_infifo_size);
   FIFO#(EntropyDecOT)      outfifo     <- mkFIFO;
   FIFO#(EntropyDecOT_InverseTrans) outfifo_ITB <- mkFIFO;
   Reg#(State)              state       <- mkReg(Start);   
   Reg#(Bit#(2))            nalrefidc   <- mkReg(0);
   Reg#(Bit#(5))            nalunittype <- mkReg(0);
   Reg#(Buffer)             buffer      <- mkReg(0);
   Reg#(Bufcount)           bufcount    <- mkReg(0);

   //saved syntax elements
   Reg#(Bit#(5))              spsseq_parameter_set_id                    <- mkReg(0);
   Reg#(Bit#(5))              spslog2_max_frame_num                      <- mkReg(0);
   Reg#(Bit#(5))              spslog2_max_pic_order_cnt_lsb              <- mkReg(0);
   Reg#(Bit#(2))              spspic_order_cnt_type                      <- mkReg(0);
   Reg#(Bit#(1))              spsdelta_pic_order_always_zero_flag        <- mkReg(0);
   Reg#(Bit#(8))              spsnum_ref_frames_in_pic_order_cnt_cycle   <- mkReg(0);
   Reg#(Bit#(8))              ppspic_parameter_set_id                    <- mkReg(0);
   Reg#(Bit#(1))              ppspic_order_present_flag                  <- mkReg(0);
   Reg#(Bit#(1))              ppsdeblocking_filter_control_present_flag  <- mkReg(0);
   Reg#(Bit#(4))              shslice_type                               <- mkReg(0);
   Reg#(Bit#(3))              shdmemory_management_control_operation     <- mkReg(0);
   Reg#(MbType)               sdmmbtype                                  <- mkReg(I_NxN);
   Reg#(Bit#(4))              sdmcodedBlockPatternLuma                   <- mkReg(0);
   Reg#(Bit#(2))              sdmcodedBlockPatternChroma                 <- mkReg(0);
   Reg#(Bit#(5))              sdmrTotalCoeff                             <- mkReg(0);
   Reg#(Bit#(2))              sdmrTrailingOnes                           <- mkReg(0);
   
   //derived decoding variables for slice data
   Reg#(Bit#(16))             tempreg                                    <- mkReg(0);
   Reg#(Bit#(5))              num_ref_idx_l0_active_minus1               <- mkReg(0);
   Reg#(Bit#(PicAreaSz))      currMbAddr                                 <- mkReg(0);
   Reg#(Bit#(3))              temp3bit0                                  <- mkReg(0);
   Reg#(Bit#(3))              temp3bit1                                  <- mkReg(0);
   Reg#(Bit#(3))              temp3bit2                                  <- mkReg(0);
   Reg#(Bit#(3))              temp3bit3                                  <- mkReg(0);
   Reg#(Bit#(5))              temp5bit                                   <- mkReg(0);
   Reg#(Bit#(5))              temp5bit2                                  <- mkReg(0);
   Reg#(Bit#(5))              maxNumCoeff                                <- mkReg(0);
   FIFO#(Bit#(13))            cavlcFIFO                                  <- mkSizedFIFO(16);
   Calc_nC                    calcnc                                     <- mkCalc_nC();
   Reg#(Bit#(1))              residualChroma                             <- mkReg(0);
   Reg#(Bit#(5))              totalCoeff                                 <- mkReg(0);
   Reg#(Bit#(4))              zerosLeft                                  <- mkReg(0);

   //exp-golomb 32-bit version states
   Reg#(Bufcount)             egnumbits                                  <- mkReg(0);

   //extra-buffering states
   Reg#(Bit#(32))             extrabuffer                                <- mkReg(0);
   Reg#(Bit#(3))              extrabufcount                              <- mkReg(0);
   Reg#(Bit#(1))              extraendnalflag                            <- mkReg(0);
   Reg#(Bit#(1))              endnalflag                                 <- mkReg(0);
   

   //-----------------------------------------------------------
   // Rules

   rule startup (state matches Start);
      case (infifo.first()) matches
	 tagged NewUnit :
	    begin
	       infifo.deq();
	       state <= NewUnit;
	       buffer <= 0;
	       bufcount <= 0;
	       extrabuffer <= 0;
	       extrabufcount <= 0;
	       extraendnalflag <= 0;
	       endnalflag <= 0;
	    end
	 tagged RbspByte .rdata :
	    begin
	       infifo.deq();
	    end
	 tagged EndOfFile :
	    begin
	       infifo.deq();
	       outfifo.enq(EndOfFile);
	       $display( "INFO EntropyDec: EndOfFile reached" );
	    end
      endcase
   endrule

   
   rule newunit (state matches NewUnit);
      case (infifo.first()) matches
	 tagged NewUnit : state <= Start;
	 tagged RbspByte .rdata :
	    begin
	       infifo.deq();
	       nalrefidc <= rdata[6:5];
	       nalunittype <= rdata[4:0];
	       case (rdata[4:0])
		  1 : state <= tagged CodedSlice 0;
		  5 : state <= tagged CodedSlice 0;
		  6 : state <= SEI;
		  7 : state <= tagged SPS 0;
		  8 : state <= tagged PPS 0;
		  9 : state <= AUD;
		  10: state <= EndSequence;
		  11: state <= EndStream;
		  12: state <= Filler;
		  default:
		  begin
		     $display( "ERROR EntropyDec: NAL Unit Type = %d", rdata[4:0] );
		     state <= Start;
		  end
	       endcase
	       $display("ccl2newunit");
	       $display("ccl2rbspbyte %h", rdata);
	       outfifo.enq(tagged NewUnit rdata);
	       outfifo_ITB.enq(tagged NewUnit rdata);
	    end
	 tagged EndOfFile : state <= Start;
      endcase
   endrule


   rule fillextrabuffer (state != Start
			 && state != NewUnit
			 && extrabufcount < 4
			 && extraendnalflag == 0);
      if(infifo.first() matches tagged RbspByte .dbyte)
	 begin
	    case ( extrabufcount )
	       0: extrabuffer <= {dbyte, extrabuffer[23:0]};
	       1: extrabuffer <= {extrabuffer[31:24],dbyte,extrabuffer[15:0]};
	       2: extrabuffer <= {extrabuffer[31:16],dbyte,extrabuffer[7:0]};
	       3: extrabuffer <= {extrabuffer[31:8],dbyte};
	       default: $display( "ERROR EntropyDec: fillextrabuffer default case_" );
	    endcase
	    extrabufcount <= extrabufcount + 1;
	    infifo.deq();
	    //$display( "TRACE EntropyDec: fillextrabuffer RbspByte %h %h %h", dbyte, extrabufcount, extrabuffer);
	 end
      else
	 begin
	    if(extrabufcount != 0)
	       extraendnalflag <= 1;
	    //$display( "TRACE EntropyDec: fillextrabuffer else %h", extrabufcount);
	 end
   endrule
   

   rule fillbuffer (state != Start
		    && state != NewUnit
		    && bufcount<=truncate(buffersize-32)
		    && (extrabufcount == 4 || extraendnalflag == 1)
		    && endnalflag == 0);//predicate not sure
      Buffer temp = zeroExtend(extrabuffer);
      Bufcount temp2 = truncate(buffersize)-bufcount-32;
      buffer <= (buffer | (temp << temp2));
      case ( extrabufcount )
	 4: bufcount <= bufcount+32;
	 3: bufcount <= bufcount+24;
	 2: bufcount <= bufcount+16;
	 1: bufcount <= bufcount+8;
	 default: $display( "ERROR EntropyDec: fillbuffer default case" );
      endcase
      extrabuffer <= 0;
      extrabufcount <= 0;
      if(infifo.first()==NewUnit || infifo.first()==EndOfFile)
	 endnalflag <= 1;
      //$display( "TRACE EntropyDec: fillbuffer RbspByte %h %h %h %h %h %h %h %h", extrabufcount, bufcount, extrabuffer, temp, temp2, (temp << zeroExtend(temp2)), buffer, (buffer | (temp << zeroExtend(temp2))));
   endrule


   rule parser (state != Start
                &&& state != NewUnit
		&&& (bufcount > truncate(buffersize-32) || endnalflag == 1));//predicate not sure
      //$display( "TRACE EntropyDec: fillbuffer RbspByte %h %h", bufcount, buffer );
      
      Bufcount numbitsused = 0;
      State nextstate = Start;
      Int#(16) tempint = 0;
      Int#(32) tempint32 = 0;
      
      case ( state ) matches
	 tagged CodedSlice .step : 
	    begin
	       case ( step )
		  0:
		  begin
		     $display( "ccl2SHfirst_mb_in_slice %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHfirst_mb_in_slice truncate(expgolomb_unsigned(buffer)));
		     currMbAddr <= truncate(expgolomb_unsigned(buffer));
		     calcnc.initialize(truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 1;
		  end
		  1:
		  begin
		     $display( "ccl2SHslice_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHslice_type truncate(expgolomb_unsigned(buffer)));
		     shslice_type <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 2;
		  end
		  2:
		  begin
		     $display( "ccl2SHpic_parameter_set_id %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHpic_parameter_set_id truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 3;
		     if(ppspic_parameter_set_id != truncate(expgolomb_unsigned(buffer))) $display( "ERROR EntropyDec: pic_parameter_set_id don't match" );
		  end
		  3:
		  begin
		     Bit#(16) tttt = buffer[buffersize-1:buffersize-16];
		     tttt = tttt >> 16 - spslog2_max_frame_num;
		     $display( "ccl2SHframe_num %0d", tttt );
		     outfifo.enq(tagged SHframe_num tttt);
		     numbitsused = zeroExtend(spslog2_max_frame_num);
		     nextstate = tagged CodedSlice 4;
		  end
		  4:
		  begin
		     if(nalunittype == 5)
			begin
			   $display( "ccl2SHidr_pic_id %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SHidr_pic_id truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     nextstate = tagged CodedSlice 5;
		  end
		  5:
		  begin
		     if(spspic_order_cnt_type == 0)
			begin
			   Bit#(16) tttt = buffer[buffersize-1:buffersize-16];
			   tttt = tttt >> 16 - spslog2_max_pic_order_cnt_lsb;
			   $display( "ccl2SHpic_order_cnt_lsb %0d", tttt );
			   outfifo.enq(tagged SHpic_order_cnt_lsb tttt);
			   numbitsused = zeroExtend(spslog2_max_pic_order_cnt_lsb);
			   nextstate = tagged CodedSlice 6;
			end
		     else
			nextstate = tagged CodedSlice 7;
		  end
		  6:
		  begin
		     if(ppspic_order_present_flag == 1)
			begin
			   if(egnumbits == 0)
			      begin
				 Bufcount tempbufcount = expgolomb_numbits32(buffer);
				 egnumbits <= tempbufcount;
				 numbitsused = tempbufcount-1;
				 nextstate = tagged CodedSlice 6;
			      end
			   else
			      begin
				 tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
				 $display( "ccl2SHdelta_pic_order_cnt_bottom %0d", tempint32 );
				 outfifo.enq(tagged SHdelta_pic_order_cnt_bottom truncate(expgolomb_signed32(buffer,egnumbits)));
				 egnumbits <= 0;
				 numbitsused = egnumbits;
				 nextstate = tagged CodedSlice 7;
			      end
			end
		     else
			nextstate = tagged CodedSlice 7;
		  end
		  7:
		  begin
		     if(spspic_order_cnt_type == 1 && spsdelta_pic_order_always_zero_flag == 0)
			begin
			   if(egnumbits == 0)
			      begin
				 Bufcount tempbufcount = expgolomb_numbits32(buffer);
				 egnumbits <= tempbufcount;
				 numbitsused = tempbufcount-1;
				 nextstate = tagged CodedSlice 7;
			      end
			   else
			      begin
				 tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
				 $display( "ccl2SHdelta_pic_order_cnt0 %0d", tempint32 );
				 outfifo.enq(tagged SHdelta_pic_order_cnt0 truncate(expgolomb_signed32(buffer,egnumbits)));
				 egnumbits <= 0;
				 numbitsused = egnumbits;
				 nextstate = tagged CodedSlice 8;
			      end
			end
		     else
			nextstate = tagged CodedSlice 9;
		  end
		  8:
		  begin
		     if(ppspic_order_present_flag == 1)
			begin
			   if(egnumbits == 0)
			      begin
				 Bufcount tempbufcount = expgolomb_numbits32(buffer);
				 egnumbits <= tempbufcount;
				 numbitsused = tempbufcount-1;
				 nextstate = tagged CodedSlice 8;
			      end
			   else
			      begin
				 tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
				 $display( "ccl2SHdelta_pic_order_cnt1 %0d", tempint32 );
				 outfifo.enq(tagged SHdelta_pic_order_cnt1 truncate(expgolomb_signed32(buffer,egnumbits)));
				 egnumbits <= 0;
				 numbitsused = egnumbits;
				 nextstate = tagged CodedSlice 9;
			      end
			end
		     else
			nextstate = tagged CodedSlice 9;
		  end
		  9:
		  begin
		     if(shslice_type == 0 || shslice_type == 5)
			begin
			   $display( "ccl2SHnum_ref_idx_active_override_flag %0d", buffer[buffersize-1] );
			   outfifo.enq(tagged SHnum_ref_idx_active_override_flag buffer[buffersize-1]);
			   numbitsused = 1;
			   if(buffer[buffersize-1] == 1)
			      nextstate = tagged CodedSlice 10;
			   else
			      nextstate = tagged CodedSlice 11;
			end
		     else
			nextstate = tagged CodedSlice 11;
		  end
		  10:
		  begin
		     $display( "ccl2SHnum_ref_idx_l0_active %0d", expgolomb_unsigned(buffer)+1 );
		     outfifo.enq(tagged SHnum_ref_idx_l0_active truncate(expgolomb_unsigned(buffer)+1));
		     num_ref_idx_l0_active_minus1 <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 11;
		  end
		  11:
		  begin
		     if(shslice_type != 2 && shslice_type != 7)
			begin
			   $display( "ccl2SHRref_pic_list_reordering_flag_l0 %0d", buffer[buffersize-1] );
			   outfifo.enq(tagged SHRref_pic_list_reordering_flag_l0 buffer[buffersize-1]);
			   numbitsused = 1;
			   if(buffer[buffersize-1] == 1)
			      nextstate = tagged CodedSlice 12;
			   else
			      nextstate = tagged CodedSlice 15;
			end
		     else
			nextstate = tagged CodedSlice 15;
		  end
		  12:
		  begin 
		     $display( "ccl2SHRreordering_of_pic_nums_idc %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHRreordering_of_pic_nums_idc truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     if(expgolomb_unsigned(buffer)==0 || expgolomb_unsigned(buffer)==1)
			nextstate = tagged CodedSlice 13;
		     else if(expgolomb_unsigned(buffer)==2)
			nextstate = tagged CodedSlice 14;
		     else
			nextstate = tagged CodedSlice 15;
		  end
		  13:
		  begin
		     Bit#(17) temp17 = zeroExtend(expgolomb_unsigned(buffer)) + 1;
		     $display( "ccl2SHRabs_diff_pic_num %0d", temp17 );
		     outfifo.enq(tagged SHRabs_diff_pic_num temp17);
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 12;
		  end
		  14:
		  begin
		     $display( "ccl2SHRlong_term_pic_num %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHRlong_term_pic_num truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 12;
		  end
		  15:
		  begin
		     if(nalrefidc == 0)
			nextstate = tagged CodedSlice 23;
		     else
			begin
			   if(nalunittype == 5)
			      begin
				 $display( "ccl2SHDno_output_of_prior_pics_flag %0d", buffer[buffersize-1] );
				 outfifo.enq(tagged SHDno_output_of_prior_pics_flag buffer[buffersize-1]);
				 numbitsused = 1;
				 nextstate = tagged CodedSlice 16;
			      end
			   else
			      nextstate = tagged CodedSlice 17;
			end
		  end
		  16:
		  begin
		     $display( "ccl2SHDlong_term_reference_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SHDlong_term_reference_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged CodedSlice 23;
		  end
		  17:
		  begin
		     $display( "ccl2SHDadaptive_ref_pic_marking_mode_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SHDadaptive_ref_pic_marking_mode_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     if(buffer[buffersize-1] == 1)
			nextstate = tagged CodedSlice 18;
		     else 
			nextstate = tagged CodedSlice 23;
		  end
		  18:
		  begin
		     $display( "ccl2SHDmemory_management_control_operation %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SHDmemory_management_control_operation truncate(expgolomb_unsigned(buffer)));
		     shdmemory_management_control_operation <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     if(expgolomb_unsigned(buffer)!=0)
			nextstate = tagged CodedSlice 19;
		     else
			nextstate = tagged CodedSlice 23;
		  end
		  19:
		  begin
		     if(shdmemory_management_control_operation==1 || shdmemory_management_control_operation==3)
		       	begin
			   Bit#(17) temp17 = zeroExtend(expgolomb_unsigned(buffer)) + 1;
			   $display( "ccl2SHDdifference_of_pic_nums %0d", temp17 );
			   outfifo.enq(tagged SHDdifference_of_pic_nums temp17);
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged CodedSlice 20;
			end
		     else
			nextstate = tagged CodedSlice 20;
		  end
		  20:
		  begin
		     if(shdmemory_management_control_operation==2)
		       	begin
			   $display( "ccl2SHDlong_term_pic_num %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SHDlong_term_pic_num truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged CodedSlice 21;
			end
		     else
			nextstate = tagged CodedSlice 21;
		  end
		  21:
		  begin
		     if(shdmemory_management_control_operation==3 || shdmemory_management_control_operation==6)
		       	begin
			   $display( "ccl2SHDlong_term_frame_idx %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SHDlong_term_frame_idx truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged CodedSlice 22;
			end
		     else
			nextstate = tagged CodedSlice 22;
		  end
		  22:
		  begin
		     if(shdmemory_management_control_operation==4)
		       	begin
			   $display( "ccl2SHDmax_long_term_frame_idx_plus1 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SHDmax_long_term_frame_idx_plus1 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged CodedSlice 18;
			end
		     else
			nextstate = tagged CodedSlice 18;
		  end
		  23:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SHslice_qp_delta %0d", tempint );
		     outfifo_ITB.enq(tagged SHslice_qp_delta truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 24;
		  end
		  24:
		  begin
		     if(ppsdeblocking_filter_control_present_flag==1)
			begin
			   $display( "ccl2SHdisable_deblocking_filter_idc %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SHdisable_deblocking_filter_idc truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   if(expgolomb_unsigned(buffer)!=1)
			      nextstate = tagged CodedSlice 25;
			   else
			      nextstate = tagged CodedSlice 27;
			end
		     else
		        nextstate = tagged CodedSlice 27;
		  end
		  25:
		  begin
		     tempint = unpack(expgolomb_signed(buffer) << 1);
		     $display( "ccl2SHslice_alpha_c0_offset %0d", tempint );
		     outfifo.enq(tagged SHslice_alpha_c0_offset truncate(expgolomb_signed(buffer) << 1));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 26;
		  end
		  26:
		  begin
		     tempint = unpack(expgolomb_signed(buffer) << 1);
		     $display( "ccl2SHslice_beta_offset %0d", tempint );
		     outfifo.enq(tagged SHslice_beta_offset truncate(expgolomb_signed(buffer) << 1));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged CodedSlice 27;
		  end
		  27:
		  begin
		     nextstate = tagged SliceData 0;
		  end
		  default: $display( "ERROR EntropyDec: CodedSlice default step" );
	       endcase	       
	    end
	 tagged SEI :
	    begin
	       nextstate = Start;
	       $display( "INFO EntropyDec: SEI data thrown away" );
	    end
	 tagged SPS .step : 
	    begin
	       case ( step )
		  0:
		  begin
		     Bit#(8) outputdata = buffer[buffersize-1:buffersize-8];
		     $display( "INFO EntropyDec: profile_idc = %d", outputdata );
		     outputdata = buffer[buffersize-9:buffersize-16];
		     $display( "INFO EntropyDec: constraint_set = %b", outputdata );
		     outputdata = buffer[buffersize-17:buffersize-24];
		     $display( "INFO EntropyDec: level_idc = %d", outputdata );
		     numbitsused = 24;
		     nextstate = tagged SPS 1;
		  end
		  1:
		  begin
		     $display( "ccl2SPSseq_parameter_set_id %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSseq_parameter_set_id truncate(expgolomb_unsigned(buffer)));
		     spsseq_parameter_set_id <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 2;
		  end
		  2:
		  begin
		     $display( "ccl2SPSlog2_max_frame_num %0d", expgolomb_unsigned(buffer)+4 );
		     outfifo.enq(tagged SPSlog2_max_frame_num truncate(expgolomb_unsigned(buffer)+4));
		     spslog2_max_frame_num <= truncate(expgolomb_unsigned(buffer)+4);
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 3;
		  end
		  3:
		  begin
		     let tttt = expgolomb_unsigned(buffer);
		     $display( "ccl2SPSpic_order_cnt_type %0d", tttt );
		     outfifo.enq(tagged SPSpic_order_cnt_type truncate(tttt));
		     spspic_order_cnt_type <= truncate(tttt);
		     numbitsused = expgolomb_numbits(buffer);
		     if(tttt == 0) 
			nextstate = tagged SPS 4;
		     else if(tttt == 1) 
			nextstate = tagged SPS 5;
		     else 
			nextstate = tagged SPS 10;
		  end
		  4:
		  begin
		     $display( "ccl2SPSlog2_max_pic_order_cnt_lsb %0d", expgolomb_unsigned(buffer)+4 );
		     outfifo.enq(tagged SPSlog2_max_pic_order_cnt_lsb truncate(expgolomb_unsigned(buffer)+4));
		     spslog2_max_pic_order_cnt_lsb <= truncate(expgolomb_unsigned(buffer)+4);
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 10;
		  end
		  5:
		  begin
		     $display( "ccl2SPSdelta_pic_order_always_zero_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SPSdelta_pic_order_always_zero_flag buffer[buffersize-1]);
		     spsdelta_pic_order_always_zero_flag <= buffer[buffersize-1];
		     numbitsused = 1;
		     nextstate = tagged SPS 6;
		  end
		  6:
		  begin
		     if(egnumbits == 0)
			begin
			   Bufcount tempbufcount = expgolomb_numbits32(buffer);
			   egnumbits <= tempbufcount;
			   numbitsused = tempbufcount-1;
			   nextstate = tagged SPS 6;
			end
		     else
			begin
			   tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
			   $display( "ccl2SPSoffset_for_non_ref_pic %0d", tempint32 );
			   outfifo.enq(tagged SPSoffset_for_non_ref_pic truncate(expgolomb_signed32(buffer,egnumbits)));
			   egnumbits <= 0;
			   numbitsused = egnumbits;
			   nextstate = tagged SPS 7;
			end
		  end
		  7:
		  begin
		     if(egnumbits == 0)
			begin
			   Bufcount tempbufcount = expgolomb_numbits32(buffer);
			   egnumbits <= tempbufcount;
			   numbitsused = tempbufcount-1;
			   nextstate = tagged SPS 7;
			end
		     else
			begin
			   tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
			   $display( "ccl2SPSoffset_for_top_to_bottom_field %0d", tempint32 );
			   outfifo.enq(tagged SPSoffset_for_top_to_bottom_field truncate(expgolomb_signed32(buffer,egnumbits)));
			   egnumbits <= 0;
			   numbitsused = egnumbits;
			   nextstate = tagged SPS 8;
			end
		  end
		  8:
		  begin
		     $display( "ccl2SPSnum_ref_frames_in_pic_order_cnt_cycle %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSnum_ref_frames_in_pic_order_cnt_cycle truncate(expgolomb_unsigned(buffer)));
		     spsnum_ref_frames_in_pic_order_cnt_cycle <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 9;
		  end
		  9:
		  begin
		     if(spsnum_ref_frames_in_pic_order_cnt_cycle == 0) 
			nextstate = tagged SPS 10;
		     else
			begin
			   if(egnumbits == 0)
			      begin
				 Bufcount tempbufcount = expgolomb_numbits32(buffer);
				 egnumbits <= tempbufcount;
				 numbitsused = tempbufcount-1;
				 nextstate = tagged SPS 9;
			      end
			   else
			      begin
				 tempint32 = unpack(expgolomb_signed32(buffer,egnumbits));
				 $display( "ccl2SPSoffset_for_ref_frame %0d", tempint32 );
				 outfifo.enq(tagged SPSoffset_for_ref_frame truncate(expgolomb_signed32(buffer,egnumbits)));
				 egnumbits <= 0;
				 spsnum_ref_frames_in_pic_order_cnt_cycle <= spsnum_ref_frames_in_pic_order_cnt_cycle - 1;
				 numbitsused = egnumbits;
				 nextstate = tagged SPS 9;
			      end
			end
		  end
		  10:
		  begin
		     $display( "ccl2SPSnum_ref_frames %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSnum_ref_frames truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 11;
		  end
		  11:
		  begin
		     $display( "ccl2SPSgaps_in_frame_num_allowed_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SPSgaps_in_frame_num_allowed_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged SPS 12;
		  end
		  12:
		  begin
		     $display( "ccl2SPSpic_width_in_mbs %0d", expgolomb_unsigned(buffer)+1 );
		     outfifo.enq(tagged SPSpic_width_in_mbs truncate(expgolomb_unsigned(buffer)+1));
		     calcnc.initialize_picWidth(truncate(expgolomb_unsigned(buffer)+1));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 13;
		  end
		  13:
		  begin
		     $display( "ccl2SPSpic_height_in_map_units %0d", expgolomb_unsigned(buffer)+1 );
		     outfifo.enq(tagged SPSpic_height_in_map_units truncate(expgolomb_unsigned(buffer)+1));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 14;
		  end
		  14:
		  begin
		     //SPSframe_mbs_only_flag = 1 for baseline
		     numbitsused = 1;
		     nextstate = tagged SPS 15;
		  end
		  15:
		  begin
		     $display( "ccl2SPSdirect_8x8_inference_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SPSdirect_8x8_inference_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged SPS 16;
		  end
		  16:
		  begin
		     $display( "ccl2SPSframe_cropping_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged SPSframe_cropping_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     if(buffer[buffersize-1] == 1) 
			nextstate = tagged SPS 17;
		     else 
			nextstate = tagged SPS 21;
		  end
		  17:
		  begin
		     $display( "ccl2SPSframe_crop_left_offset %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSframe_crop_left_offset truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 18;
		  end
		  18:
		  begin
		     $display( "ccl2SPSframe_crop_right_offset %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSframe_crop_right_offset truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 19;
		  end
		  19:
		  begin
		     $display( "ccl2SPSframe_crop_top_offset %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSframe_crop_top_offset truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 20;
		  end
		  20:
		  begin
		     $display( "ccl2SPSframe_crop_bottom_offset %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SPSframe_crop_bottom_offset truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SPS 21;
		  end
		  21:
		  begin
		     nextstate = Start;
		     $display( "INFO EntropyDec:VUI data thrown away" );
		  end
		  default: $display( "ERROR EntropyDec: SPS default step" );
	       endcase
	    end
	 tagged PPS .step : 
	    begin
	       case ( step )
		  0:
		  begin
		     ppspic_parameter_set_id <= truncate(expgolomb_unsigned(buffer));
		     $display( "ccl2PPSpic_parameter_set_id %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged PPSpic_parameter_set_id truncate(expgolomb_unsigned(buffer)));
		     outfifo_ITB.enq(tagged PPSpic_parameter_set_id truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 1;
		  end
		  1:
		  begin
		     $display( "ccl2PPSseq_parameter_set_id %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged PPSseq_parameter_set_id truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 2;
		     if(spsseq_parameter_set_id != truncate(expgolomb_unsigned(buffer))) 
			$display( "ERROR EntropyDec: seq_parameter_set_id don't match" );
		  end
		  2:
		  begin
		     //PPSentropy_coding_mode_flag = 0 for baseline
		     numbitsused = 1;
		     nextstate = tagged PPS 3;
		  end
		  3:
		  begin
		     ppspic_order_present_flag <= buffer[buffersize-1];
		     $display( "ccl2PPSpic_order_present_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged PPSpic_order_present_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged PPS 4;
		  end
		  4:
		  begin
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 5;
		     if(expgolomb_unsigned(buffer)+1 != 1) 
			$display( "ERROR EntropyDec: PPSnum_slice_groups not equal to 1" );//=1 for main
		  end
		  5:
		  begin
		     $display( "ccl2PPSnum_ref_idx_l0_active %0d", expgolomb_unsigned(buffer)+1 );
		     outfifo.enq(tagged PPSnum_ref_idx_l0_active truncate(expgolomb_unsigned(buffer)+1));
		     num_ref_idx_l0_active_minus1 <= truncate(expgolomb_unsigned(buffer));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 6;
		  end
		  6:
		  begin
		     $display( "ccl2PPSnum_ref_idx_l1_active %0d", expgolomb_unsigned(buffer)+1 );
		     outfifo.enq(tagged PPSnum_ref_idx_l1_active truncate(expgolomb_unsigned(buffer)+1));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 7;
		  end
		  7:
		  begin
		     //PPSweighted_pred_flag = 0 for baseline; PPSweighted_bipred_idc = 0 for baseline
		     numbitsused = 3;
		     nextstate = tagged PPS 8;
		  end
		  8:
		  begin
		     $display( "ccl2PPSpic_init_qp %0d", expgolomb_signed(buffer)+26 );
		     outfifo_ITB.enq(tagged PPSpic_init_qp truncate(expgolomb_signed(buffer)+26));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 9;
		  end
		  9:
		  begin
		     $display( "ccl2PPSpic_init_qs %0d", expgolomb_signed(buffer)+26 );
		     outfifo_ITB.enq(tagged PPSpic_init_qs truncate(expgolomb_signed(buffer)+26));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 10;
		  end
		  10:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2PPSchroma_qp_index_offset %0d", tempint );
		     outfifo_ITB.enq(tagged PPSchroma_qp_index_offset truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged PPS 11;
		  end
		  11:
		  begin
		     ppsdeblocking_filter_control_present_flag <= buffer[buffersize-1];
		     $display( "ccl2PPSdeblocking_filter_control_present_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged PPSdeblocking_filter_control_present_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged PPS 12;
		  end
		  12:
		  begin
		     $display( "ccl2PPSconstrained_intra_pred_flag %0d", buffer[buffersize-1] );
		     outfifo.enq(tagged PPSconstrained_intra_pred_flag buffer[buffersize-1]);
		     numbitsused = 1;
		     nextstate = tagged PPS 13;
		  end
		  13:
		  begin
		     //PPSredundant_pic_cnt_present_flag = 0 for main
		     numbitsused = 1;
		     nextstate = tagged PPS 14;
		     if(buffer[buffersize-1] != 0) 
			$display( "ERROR EntropyDec: PPSredundant_pic_cnt_present_flag not equal to 0" );//=0 for main
		  end
		  14:
		  begin
		     nextstate = Start;
		  end
		  default: $display( "ERROR EntropyDec: PPS default step" );
	       endcase
	    end
	 tagged AUD :
	    begin
	       outfifo.enq(tagged AUDPrimaryPicType buffer[buffersize-1:buffersize-3]);
	       numbitsused = 3;
	       nextstate = Start;
	    end
	 tagged EndSequence : 
	    begin
	       outfifo.enq(tagged EndOfSequence);
	       nextstate = Start;
	    end
	 tagged EndStream : 
	    begin
	       outfifo.enq(tagged EndOfStream);
	       nextstate = Start;
	    end
	 tagged Filler : 
	    begin
	       nextstate = Start;
	    end
	 tagged SliceData .step : 
	    begin
	       case ( step )
		  0:
		  begin
		     if( shslice_type!=2 && shslice_type!=7 )
			begin
			   $display( "ccl2SDmb_skip_run %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDmb_skip_run truncate(expgolomb_unsigned(buffer)));
			   tempreg <= truncate(expgolomb_unsigned(buffer));
			   calcnc.nNupdate_pskip( truncate(expgolomb_unsigned(buffer)) );
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged SliceData 1;
			end
		     else
			nextstate = tagged SliceData 2;
		  end
		  1:
		  begin
		     if( tempreg>0 )
			begin
			   currMbAddr <= currMbAddr+1;//only because input assumed to comform to both baseline and main
			   tempreg <= tempreg-1;
			   nextstate = tagged SliceData 1;
			end
		     else
			begin
			   ////$display( "ccl2SDcurrMbAddr %0d", currMbAddr );
			   ////outfifo.enq(SDcurrMbAddr currMbAddr);
			   nextstate = tagged SliceData 2;
			end
		  end
		  2:
		  begin
		     if( bufcount>8 || buffer[buffersize-1]!=1 || (buffer<<1)!=0 )
			begin
			   calcnc.loadMb(currMbAddr);
			   nextstate = tagged MacroblockLayer 0;
			end
		     else
			nextstate = tagged SliceData 3;
		  end
		  3:
		  begin
		     currMbAddr <= currMbAddr+1;//only because input assumed to comform to both baseline and main
		     if( bufcount>8 || buffer[buffersize-1]!=1 || (buffer<<1)!=0 )
			nextstate = tagged SliceData 0;
		     else
			nextstate = Start;
		  end
		  default: $display( "ERROR EntropyDec: SliceData default step" );
	       endcase
	    end
	 tagged MacroblockLayer .step : //return to SliceData 3
	    begin
	       case ( step )
		  0:
		  begin
		     $display( "ccl2SDMmb_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SDMmbtype mbtype_convert(truncate(expgolomb_unsigned(buffer)), shslice_type) );
		     outfifo_ITB.enq(tagged SDMmbtype mbtype_convert(truncate(expgolomb_unsigned(buffer)), shslice_type) );
		     sdmmbtype <= mbtype_convert(truncate(expgolomb_unsigned(buffer)), shslice_type);
		     numbitsused = expgolomb_numbits(buffer);
		     if(mbtype_convert(truncate(expgolomb_unsigned(buffer)), shslice_type) == I_PCM)
			begin
			   calcnc.nNupdate_ipcm();
			   nextstate = tagged MacroblockLayer 1;
			end
		     else
			nextstate = tagged MacroblockLayer 4;
		  end
		  1:
		  begin
		     tempreg <= 256;
		     numbitsused = zeroExtend(bufcount[2:0]);
		     nextstate = tagged MacroblockLayer 2;
		  end
		  2:
		  begin
		     if( tempreg>0 )
			begin
			   Bit#(8) outputdata = buffer[buffersize-1:buffersize-8];
			   $display( "ccl2SDMpcm_sample_luma %0d", outputdata );
			   outfifo.enq(tagged SDMpcm_sample_luma outputdata);
			   tempreg <= tempreg-1;
			   numbitsused = 8;
			   nextstate = tagged MacroblockLayer 2;
			end
		     else
			begin
			   tempreg <= 128;
			   nextstate = tagged MacroblockLayer 3;
			end
		  end
		  3:
		  begin
		     if( tempreg>0 )
			begin
			   Bit#(8) outputdata = buffer[buffersize-1:buffersize-8];
			   $display( "ccl2SDMpcm_sample_chroma %0d", outputdata );
			   outfifo.enq(tagged SDMpcm_sample_chroma outputdata);
			   tempreg <= tempreg-1;
			   numbitsused = 8;
			   nextstate = tagged MacroblockLayer 3;
			end
		     else
			   nextstate = tagged SliceData 3;
		  end
		  4:
		  begin
		     if(sdmmbtype != I_NxN
			&&& mbPartPredMode(sdmmbtype,0) != Intra_16x16
			&&& numMbPart(sdmmbtype) == 4)
			nextstate = tagged SubMbPrediction 0;
		     else
			nextstate = tagged MbPrediction 0;
		  end
		  5:
		  begin
		     if(mbPartPredMode(sdmmbtype,0) != Intra_16x16)
			begin
			   $display( "ccl2SDMcoded_block_pattern %0d", expgolomb_coded_block_pattern(buffer,sdmmbtype) );
			   ////outfifo.enq(SDMcoded_block_pattern expgolomb_coded_block_pattern(buffer,sdmmbtype));
			   sdmcodedBlockPatternLuma <= expgolomb_coded_block_pattern(buffer,sdmmbtype)[3:0];
			   sdmcodedBlockPatternChroma <= expgolomb_coded_block_pattern(buffer,sdmmbtype)[5:4];
			   numbitsused = expgolomb_numbits(buffer);
			end
		     else
			begin
			   if(sdmmbtype matches tagged I_16x16 {intra16x16PredMode:.tempv1, codedBlockPatternChroma:.tempv2, codedBlockPatternLuma:.tempv3})
			      begin
				 sdmcodedBlockPatternLuma <= {tempv3,tempv3,tempv3,tempv3};
				 sdmcodedBlockPatternChroma <= tempv2;
			      end
			   else
			      $display( "ERROR EntropyDec: MacroblockLayer 5 sdmmbtype not I_16x16" );
			end
		     nextstate = tagged MacroblockLayer 6;
		  end
		  6:
		  begin
		     if(sdmcodedBlockPatternLuma > 0
			|| sdmcodedBlockPatternChroma > 0
			|| mbPartPredMode(sdmmbtype,0) == Intra_16x16)
			begin
			   tempint = unpack(expgolomb_signed(buffer));
			   $display( "ccl2SDMmb_qp_delta %0d", tempint );
			   outfifo_ITB.enq(tagged SDMmb_qp_delta truncate(expgolomb_signed(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     residualChroma <= 0;
		     temp5bit <= 0;
		     maxNumCoeff <= 16;
		     nextstate = tagged ResidualBlock 0;
		  end
		  default: $display( "ERROR EntropyDec: MacroblockLayer default step" );
	       endcase
	    end
	 tagged MbPrediction .step : //return to tagged MacroblockLayer 5
	    begin
	       case ( step )
		  0:
		  begin
		     if(mbPartPredMode(sdmmbtype,0) == Intra_16x16)
			begin
			   $display( "ccl2SDMMintra_chroma_pred_mode %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMMintra_chroma_pred_mode truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged MacroblockLayer 5;
			end
		     else if(mbPartPredMode(sdmmbtype,0) == Intra_4x4)
			begin
			   temp5bit <= 16;
			   nextstate = tagged MbPrediction 1;
			end
		     else if(num_ref_idx_l0_active_minus1 > 0)
			begin
			   temp3bit0 <= numMbPart(sdmmbtype);
			   nextstate = tagged MbPrediction 2;
			end
		     else
			begin
			   temp3bit0 <= numMbPart(sdmmbtype);
			   nextstate = tagged MbPrediction 3;
			end
		  end
		  1:
		  begin
		     if(temp5bit == 0)
			begin
			   $display( "ccl2SDMMintra_chroma_pred_mode %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMMintra_chroma_pred_mode truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			   nextstate = tagged MacroblockLayer 5;
			end
		     else
			begin
			   ////$display( "ccl2SDMMprev_intra4x4_pred_mode_flag %0d", buffer[buffersize-1] );
			   if(buffer[buffersize-1] == 0)
			      begin
				 Bit#(4) tttt = buffer[buffersize-1:buffersize-4];
				 $display( "ccl2SDMMrem_intra4x4_pred_mode %0d", tttt );
				 outfifo.enq(tagged SDMMrem_intra4x4_pred_mode tttt);
				 numbitsused = 4;
			      end
			   else
			      begin
				 outfifo.enq(tagged SDMMrem_intra4x4_pred_mode 4'b1000);
				 numbitsused = 1;
			      end
			   temp5bit <= temp5bit-1;
			   nextstate = tagged MbPrediction 1;
			end
		  end
		  2:
		  begin
		     if(num_ref_idx_l0_active_minus1 == 1)
			begin
			   $display( "ccl2SDMMref_idx_l0 %0d", 1-buffer[buffersize-1] );
			   outfifo.enq(tagged SDMMref_idx_l0 zeroExtend(1-buffer[buffersize-1]));
			   numbitsused = 1;
			end
		     else
			begin
			   $display( "ccl2SDMMref_idx_l0 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMMref_idx_l0 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     if(temp3bit0 == 1)
			begin
			   temp3bit0 <= numMbPart(sdmmbtype);
			   nextstate = tagged MbPrediction 3;
			end
		     else
			begin
			   temp3bit0 <= temp3bit0-1;
			   nextstate = tagged MbPrediction 2;
			end
		  end
		  3:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMMmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMMmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged MbPrediction 4;
		  end
		  4:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMMmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMMmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     temp3bit0 <= temp3bit0-1;
		     if(temp3bit0 == 1)
			nextstate = tagged MacroblockLayer 5;
		     else
			nextstate = tagged MbPrediction 3;
		  end
		  default: $display( "ERROR EntropyDec: MbPrediction default step" );
	       endcase
	    end
	 tagged SubMbPrediction .step : //return to MacroblockLayer 5
	    begin
	       case ( step )
		  0:
		  begin
		     $display( "ccl2SDMSsub_mb_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SDMSsub_mb_type truncate(expgolomb_unsigned(buffer)));
		     temp3bit0 <= numSubMbPart(truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 1;
		  end
		  1:
		  begin
		     $display( "ccl2SDMSsub_mb_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SDMSsub_mb_type truncate(expgolomb_unsigned(buffer)));
		     temp3bit1 <= numSubMbPart(truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 2;
		  end
		  2:
		  begin
		     $display( "ccl2SDMSsub_mb_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SDMSsub_mb_type truncate(expgolomb_unsigned(buffer)));
		     temp3bit2 <= numSubMbPart(truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 3;
		  end
		  3:
		  begin
		     $display( "ccl2SDMSsub_mb_type %0d", expgolomb_unsigned(buffer) );
		     outfifo.enq(tagged SDMSsub_mb_type truncate(expgolomb_unsigned(buffer)));
		     temp3bit3 <= numSubMbPart(truncate(expgolomb_unsigned(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     if(num_ref_idx_l0_active_minus1 > 0
			      && sdmmbtype != P_8x8ref0)
			nextstate = tagged SubMbPrediction 4;
		     else
			nextstate = tagged SubMbPrediction 8;
		  end
		  4:
		  begin
		     if(num_ref_idx_l0_active_minus1 == 1)
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", 1-buffer[buffersize-1] );
			   outfifo.enq(tagged SDMSref_idx_l0 zeroExtend(1-buffer[buffersize-1]));
			   numbitsused = 1;
			end
		     else
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMSref_idx_l0 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     nextstate = tagged SubMbPrediction 5;
		  end
		  5:
		  begin
		     if(num_ref_idx_l0_active_minus1 == 1)
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", 1-buffer[buffersize-1] );
			   outfifo.enq(tagged SDMSref_idx_l0 zeroExtend(1-buffer[buffersize-1]));
			   numbitsused = 1;
			end
		     else
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMSref_idx_l0 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     nextstate = tagged SubMbPrediction 6;
		  end
		  6:
		  begin
		     if(num_ref_idx_l0_active_minus1 == 1)
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", 1-buffer[buffersize-1] );
			   outfifo.enq(tagged SDMSref_idx_l0 zeroExtend(1-buffer[buffersize-1]));
			   numbitsused = 1;
			end
		     else
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMSref_idx_l0 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     nextstate = tagged SubMbPrediction 7;
		  end
		  7:
		  begin
		     if(num_ref_idx_l0_active_minus1 == 1)
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", 1-buffer[buffersize-1] );
			   outfifo.enq(tagged SDMSref_idx_l0 zeroExtend(1-buffer[buffersize-1]));
			   numbitsused = 1;
			end
		     else
			begin
			   $display( "ccl2SDMSref_idx_l0 %0d", expgolomb_unsigned(buffer) );
			   outfifo.enq(tagged SDMSref_idx_l0 truncate(expgolomb_unsigned(buffer)));
			   numbitsused = expgolomb_numbits(buffer);
			end
		     nextstate = tagged SubMbPrediction 8;
		  end
		  8:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 9;
		  end
		  9:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     temp3bit0 <= temp3bit0-1;
		     if(temp3bit0 == 1)
			nextstate = tagged SubMbPrediction 10;
		     else
			nextstate = tagged SubMbPrediction 8;
		  end
		  10:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 11;
		  end
		  11:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     temp3bit1 <= temp3bit1-1;
		     if(temp3bit1 == 1)
			nextstate = tagged SubMbPrediction 12;
		     else
			nextstate = tagged SubMbPrediction 10;
		  end
		  12:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 13;
		  end
		  13:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     temp3bit2 <= temp3bit2-1;
		     if(temp3bit2 == 1)
			nextstate = tagged SubMbPrediction 14;
		     else
			nextstate = tagged SubMbPrediction 12;
		  end
		  14:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     nextstate = tagged SubMbPrediction 15;
		  end
		  15:
		  begin
		     tempint = unpack(expgolomb_signed(buffer));
		     $display( "ccl2SDMSmvd_l0 %0d", tempint );
		     outfifo.enq(tagged SDMSmvd_l0 truncate(expgolomb_signed(buffer)));
		     numbitsused = expgolomb_numbits(buffer);
		     temp3bit3 <= temp3bit3-1;
		     if(temp3bit3 == 1)
			nextstate = tagged MacroblockLayer 5;
		     else
			nextstate = tagged SubMbPrediction 14;
		  end
		  default: $display( "ERROR EntropyDec: SubMbPrediction default step" );
	       endcase
	    end
	 tagged ResidualBlock .step : //if(residualChroma==0) return to Residual 1;   else if(maxNumCoeff==4) return to Residual 3;   else return to Residual 5
	    begin//don't modify maxNumCoeff, residualChroma, and increment temp5bit on return
	       case ( step )
		  0:
		  begin
		     cavlcFIFO.clear();
		     if(maxNumCoeff != 4)
			begin
			   if(residualChroma == 0)
			      tempreg <= zeroExtend(calcnc.nCcalc_luma(truncate(temp5bit)));
			   else
			      tempreg <= zeroExtend(calcnc.nCcalc_chroma(truncate(temp5bit)));
			end
		     else
			tempreg <= zeroExtend(6'b111111);
		     if(mbPartPredMode(sdmmbtype,0)==Intra_16x16 && maxNumCoeff==16)
			nextstate = tagged ResidualBlock 1;
		     else if(residualChroma==0 && (sdmcodedBlockPatternLuma & (1 << (temp5bit[3:2])))==0)
			begin
			   calcnc.nNupdate_luma(truncate(temp5bit),0);
			   outfifo_ITB.enq(tagged SDMRcoeffLevelZeros maxNumCoeff);
			   nextstate = tagged ResidualBlock 5;
			end
		     else if(residualChroma==1 && maxNumCoeff==4 && (sdmcodedBlockPatternChroma & 3)==0)
			begin
			   outfifo_ITB.enq(tagged SDMRcoeffLevelZeros 4);
			   nextstate = tagged ResidualBlock 5;
			end
		     else if(residualChroma==1 && maxNumCoeff!=4 && (sdmcodedBlockPatternChroma & 2)==0)
			begin
			   calcnc.nNupdate_chroma(truncate(temp5bit),0);
			   outfifo_ITB.enq(tagged SDMRcoeffLevelZeros 15);
			   nextstate = tagged ResidualBlock 5;
			end
		     else
			nextstate = tagged ResidualBlock 1;
		     //$display( "TRACE EntropyDec: ResidualBlock 0 temp5bit = %0d", temp5bit);
		  end
		  1:
		  begin
		     Bit#(2) trailingOnesTemp = 0;
		     Bit#(5) totalCoeffTemp = 0;
		     {trailingOnesTemp,totalCoeffTemp,numbitsused} = cavlc_coeff_token( buffer, truncate(tempreg) );
		     temp3bit0 <= zeroExtend(trailingOnesTemp);//trailingOnes
		     totalCoeff <= totalCoeffTemp;
		     if(residualChroma == 0 && !(mbPartPredMode(sdmmbtype,0)==Intra_16x16 && maxNumCoeff==16))
			calcnc.nNupdate_luma(truncate(temp5bit),totalCoeffTemp);
		     else if(residualChroma == 1 && maxNumCoeff != 4)
			calcnc.nNupdate_chroma(truncate(temp5bit),totalCoeffTemp);
		     temp5bit2 <= 0;//i
		     tempreg <= 0;//levelCode temp
		     if(totalCoeffTemp > 10 && trailingOnesTemp < 3)
			temp3bit1 <= 1;//suffixLength
		     else
			temp3bit1 <= 0;//suffixLength
		     nextstate = tagged ResidualBlock 2;
		     //$display( "TRACE EntropyDec: ResidualBlock 1 nC = %0d", tempreg);
		     $display( "ccl2SDMRtotal_coeff %0d", totalCoeffTemp );
		     $display( "ccl2SDMRtrailing_ones %0d", trailingOnesTemp );
		  end
		  2:
		  begin
		     if( totalCoeff != 0 )
			begin
			   if(temp5bit2 < zeroExtend(temp3bit0))
			      begin
				 if(buffer[buffersize-1] == 1)
				    cavlcFIFO.enq(-1);
				 else
				    cavlcFIFO.enq(1);
				 numbitsused = 1;
			      end
			   else
			      begin
				 Bit#(32) buffertempshow = buffer[buffersize-1:buffersize-32];
				 Bit#(3) suffixLength = temp3bit1;
				 Bit#(4) levelSuffixSize = zeroExtend(suffixLength);
				 Bit#(4) level_prefix = cavlc_level_prefix( buffer );
				 Bit#(5) temp_level_prefix = zeroExtend(level_prefix);
				 Bit#(28) tempbuffer = buffer[buffersize-1:buffersize-28] << (temp_level_prefix+1);
				 Bit#(14) levelCode = zeroExtend(level_prefix) << suffixLength;
				 if(level_prefix == 14 && suffixLength == 0)
				    levelSuffixSize = 4;
				 else if(level_prefix == 15)
				    levelSuffixSize = 12;
				 levelCode = levelCode + zeroExtend(tempbuffer[27:16] >> (12-levelSuffixSize));//level_suffix
				 if(level_prefix == 15 && suffixLength == 0)
				    levelCode = levelCode + 15;
				 if(temp5bit2 == zeroExtend(temp3bit0) && temp3bit0 < 3)
				    levelCode = levelCode + 2;
				 if(suffixLength == 0)
				    suffixLength = 1;
				 if( suffixLength < 6 && ((levelCode+2) >> 1) > (3 << (suffixLength-1)) )
				    suffixLength = suffixLength+1;
				 if(levelCode[0] == 0)
				    cavlcFIFO.enq(truncate((levelCode+2) >> 1));
				 else
				    cavlcFIFO.enq(truncate((~levelCode) >> 1));
				 if(levelCode[0] == 0)//////////////////////////////////////////////////
				    begin
				       tempint = signExtend(unpack((levelCode+2) >> 1));
				       //$display( "TRACE EntropyDec: temp level %0d", tempint );
				    end
				 else
				    begin
				       Bit#(13) tempinttemp = truncate((~levelCode) >> 1);
				       tempint = signExtend(unpack(tempinttemp));
				       //$display( "TRACE EntropyDec: temp level %0d", tempint );
				    end///////////////////////////////////////////////////////////////////////
				 temp3bit1 <= suffixLength;
				 numbitsused = zeroExtend(level_prefix)+1+zeroExtend(levelSuffixSize);
			      end
			end
		     if( totalCoeff==0 || temp5bit2+1==totalCoeff )
			begin
			   temp5bit2 <= 0;
			   zerosLeft <= 0;
			   if(totalCoeff < maxNumCoeff)
			      nextstate = tagged ResidualBlock 3;
			   else
			      nextstate = tagged ResidualBlock 5;
			end
		     else
			begin
			   temp5bit2 <= temp5bit2 + 1;
			   nextstate = tagged ResidualBlock 2;
			end
		  end
		  3:
		  begin
		     Bit#(4) tempZerosLeft;
		     if(totalCoeff > 0)
			begin
			   {tempZerosLeft,numbitsused} = cavlc_total_zeros( buffer, truncate(totalCoeff), maxNumCoeff);
			   $display( "ccl2SDMRtotal_zeros %0d", tempZerosLeft );//////////////////////////////////////
			end
		     else
			tempZerosLeft = 0;
		     zerosLeft <= tempZerosLeft;
		     if(maxNumCoeff - totalCoeff - zeroExtend(tempZerosLeft) > 0)
			begin
			   $display( "ccl2SDMRcoeffLevelZeros %0d", maxNumCoeff - totalCoeff - zeroExtend(tempZerosLeft) );
			   outfifo_ITB.enq(tagged SDMRcoeffLevelZeros (maxNumCoeff - totalCoeff - zeroExtend(tempZerosLeft)));
			end
		     nextstate = tagged ResidualBlock 5;
		  end
		  5:
		  begin
		     if( totalCoeff > 0 )
			begin
			   tempint = signExtend(unpack(cavlcFIFO.first()));
			   $display( "ccl2SDMRcoeffLevel %0d", tempint );
			   if( zerosLeft > 0 )
			      begin
				 Bit#(4) run_before = 0;
				 if( totalCoeff > 1 )
				    {run_before,numbitsused} = cavlc_run_before( buffer, zerosLeft);
				 else
				    run_before = zerosLeft;
				 zerosLeft <= zerosLeft - run_before;
				 outfifo_ITB.enq(tagged SDMRcoeffLevelPlusZeros {level:cavlcFIFO.first(),zeros:zeroExtend(run_before)});
				 if( run_before > 0 )
				    $display( "ccl2SDMRcoeffLevelZeros %0d", run_before );
			      end
			   else
			      outfifo_ITB.enq(tagged SDMRcoeffLevelPlusZeros {level:cavlcFIFO.first(),zeros:0});
			   cavlcFIFO.deq();
			   totalCoeff <= totalCoeff-1;
			end
		     if( totalCoeff <= 1 )
			begin
			   if(residualChroma==0)
			      begin
				 nextstate = tagged ResidualBlock 0;
				 if(mbPartPredMode(sdmmbtype,0)==Intra_16x16 && maxNumCoeff==16)
				    maxNumCoeff <= 15;
				 else if(temp5bit==15)
				    begin
				       temp5bit <= 0;
				       maxNumCoeff <= 4;
				       residualChroma <= 1;
				    end
				 else
				    temp5bit <= temp5bit+1;
			      end
			   else if(maxNumCoeff==4)
			      begin
				 nextstate = tagged ResidualBlock 0;
				 if(temp5bit==1)
				    begin
				       temp5bit <= 0;
				       maxNumCoeff <= 15;
				    end
				 else
				    temp5bit <= temp5bit+1;
			      end
			   else
			      begin    
				 if(temp5bit==7)
				    begin
				       temp5bit <= 0;
				       nextstate = tagged SliceData 3;
				    end
				 else
				    begin
				       nextstate = tagged ResidualBlock 0;
				       temp5bit <= temp5bit+1;
				    end
			      end
			end
		     else
			nextstate = tagged ResidualBlock 5;
		  end
		  default: $display( "ERROR EntropyDec: ResidualBlock default step" );
	       endcase
	    end
      endcase
      
      if(numbitsused+1 > bufcount)
	 begin
	    $display( "ERROR EntropyDec: not enough bits in buffer" );
	    nextstate = Start;
	 end
      buffer <= buffer << numbitsused;
      bufcount <= bufcount-numbitsused;
      state <= nextstate;
      
   endrule
   
   
   interface Put ioin  = fifoToPut(infifo);
   interface Get ioout = fifoToGet(outfifo);
   interface Get ioout_InverseTrans = fifoToGet(outfifo_ITB);

   interface mem_client = calcnc.mem_client; 
      
endmodule

endpackage
