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
// Exp-Golomb codes
//----------------------------------------------------------------------
// 
//
//

package ExpGolomb;

import H264Types::*;


      
   //-----------------------------------------------------------
   // Helper functions
   (* noinline *)
   function Bufcount expgolomb_numbits32( Buffer inbuffer );//number of bits consumed by exp-golomb code
      Bufcount tempout = 100;
      for(Integer ii=33; ii>0; ii=ii-1)
	 begin
	    if(inbuffer[buffersize-fromInteger(ii)]==1'b1)
	       tempout = fromInteger(ii);
	 end
      return tempout;
   endfunction

   (* noinline *)
   function Bit#(33) expgolomb_codenum32( Buffer inbuffer, Bufcount egnumbits );//exp-golomb codenum calculation
      Bit#(33) tempbuffer = inbuffer[buffersize-1:buffersize-33];
      Bufcount shiftamount = 33-egnumbits;
      return (tempbuffer >> shiftamount)-1;
   endfunction

   (* noinline *)
   function Bit#(32) expgolomb_unsigned32( Buffer inbuffer, Bufcount egnumbits );//unsigned exp-golomb code calculation
      Bit#(33) codenum = expgolomb_codenum32( inbuffer, egnumbits );
      return truncate(codenum);
   endfunction

   (* noinline *)
   function Bit#(32) expgolomb_signed32( Buffer inbuffer, Bufcount egnumbits );//signed exp-golomb code calculation
      Bit#(33) codenum = expgolomb_codenum32( inbuffer, egnumbits );
      Bit#(33) tempout = (codenum+1) >> 1;
      Bit#(33) tempout2 = (codenum[0]==1 ? tempout : (~tempout)+1 );
      return truncate(tempout2);
   endfunction



   (* noinline *)
   function Bufcount expgolomb_numbits( Buffer inbuffer );//number of bits consumed by exp-golomb code
      Bufcount tempout = 100;
      for(Integer ii=17; ii>0; ii=ii-1)
	 begin
	    if(inbuffer[buffersize-fromInteger(ii)]==1'b1)
	       tempout = (fromInteger(ii)*2)-1;
	 end
      return tempout;
   endfunction

   (* noinline *)
   function Bit#(17) expgolomb_codenum( Buffer inbuffer );//exp-golomb codenum calculation
      Bufcount egnumbits = expgolomb_numbits( inbuffer ) >> 1;
      Bit#(33) tempbuffer = inbuffer[buffersize-1:buffersize-33] << egnumbits;
      Bit#(17) tempout = tempbuffer[32:16];
      Bufcount shiftamount = 17-egnumbits-1;
      return (tempout >> shiftamount)-1;
   endfunction
   
   (* noinline *)
   function Bit#(16) expgolomb_unsigned( Buffer inbuffer );//unsigned exp-golomb code calculation
      Bit#(17) codenum = expgolomb_codenum( inbuffer );
      return truncate(codenum);
   endfunction

   (* noinline *)
   function Bit#(16) expgolomb_signed( Buffer inbuffer );//signed exp-golomb code calculation
      Bit#(17) codenum = expgolomb_codenum( inbuffer );
      Bit#(17) tempout = (codenum+1) >> 1;
      Bit#(17) tempout2 = (codenum[0]==1 ? tempout : (~tempout)+1 );
      return truncate(tempout2);
   endfunction

   (* noinline *)
   function Bit#(6) expgolomb_coded_block_pattern( Buffer inbuffer, MbType mbtype );//unsigned exp-golomb code calculation
      Bit#(6) codenum = truncate(expgolomb_codenum( inbuffer ));
      if(mbPartPredMode(mbtype,0) == Intra_4x4)
	 begin
	    case(codenum)
	       0: return 47;
	       1: return 31;
	       2: return 15;
	       3: return 0;
	       4: return 23;
	       5: return 27;
	       6: return 29;
	       7: return 30;
	       8: return 7;
	       9: return 11;
	       10: return 13;
	       11: return 14;
	       12: return 39;
	       13: return 43;
	       14: return 45;
	       15: return 46;
	       16: return 16;
	       17: return 3;
	       18: return 5;
	       19: return 10;
	       20: return 12;
	       21: return 19;
	       22: return 21;
	       23: return 26;
	       24: return 28;
	       25: return 35;
	       26: return 37;
	       27: return 42;
	       28: return 44;
	       29: return 1;
	       30: return 2;
	       31: return 4;
	       32: return 8;
	       33: return 17;
	       34: return 18;
	       35: return 20;
	       36: return 24;
	       37: return 6;
	       38: return 9;
	       39: return 22;
	       40: return 25;
	       41: return 32;
	       42: return 33;
	       43: return 34;
	       44: return 36;
	       45: return 40;
	       46: return 38;
	       47: return 41;
	    endcase
	 end
      else
	 begin
	    case(codenum)
	       0: return 0;
	       1: return 16;
	       2: return 1;
	       3: return 2;
	       4: return 4;
	       5: return 8;
	       6: return 32;
	       7: return 3;
	       8: return 5;
	       9: return 10;
	       10: return 12;
	       11: return 15;
	       12: return 47;
	       13: return 7;
	       14: return 11;
	       15: return 13;
	       16: return 14;
	       17: return 6;
	       18: return 9;
	       19: return 31;
	       20: return 35;
	       21: return 37;
	       22: return 42;
	       23: return 44;
	       24: return 33;
	       25: return 34;
	       26: return 36;
	       27: return 40;
	       28: return 39;
	       29: return 43;
	       30: return 45;
	       31: return 46;
	       32: return 17;
	       33: return 18;
	       34: return 20;
	       35: return 24;
	       36: return 19;
	       37: return 21;
	       38: return 26;
	       39: return 28;
	       40: return 23;
	       41: return 27;
	       42: return 29;
	       43: return 30;
	       44: return 22;
	       45: return 25;
	       46: return 38;
	       47: return 41;
	    endcase
	 end
   endfunction



endpackage
