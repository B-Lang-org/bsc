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
// CAVLC codes
//----------------------------------------------------------------------
// 
//
//

package CAVLC;

import H264Types::*;

      
   //-----------------------------------------------------------
   // Helper functions


   (* noinline *)
   function Tuple3#(Bit#(2),Bit#(5),Bufcount) cavlc_coeff_token( Buffer inbuffer, Bit#(6) nC );
      if(nC[5] == 1)
	 begin
	    Bit#(8) buffertemp = inbuffer[buffersize-1:buffersize-8];
	    if(buffertemp[7:6]  ==  2'b01) return tuple3(0,0,2);
	    else if(buffertemp[7:2]  ==  6'b000111) return tuple3(0,1,6);
	    else if(buffertemp[7:7]  ==  1'b1) return tuple3(1,1,1);
	    else if(buffertemp[7:2]  ==  6'b000100) return tuple3(0,2,6);
	    else if(buffertemp[7:2]  ==  6'b000110) return tuple3(1,2,6);
	    else if(buffertemp[7:5]  ==  3'b001) return tuple3(2,2,3);
	    else if(buffertemp[7:2]  ==  6'b000011) return tuple3(0,3,6);
	    else if(buffertemp[7:1]  ==  7'b0000011) return tuple3(1,3,7);
	    else if(buffertemp[7:1]  ==  7'b0000010) return tuple3(2,3,7);
	    else if(buffertemp[7:2]  ==  6'b000101) return tuple3(3,3,6);
	    else if(buffertemp[7:2]  ==  6'b000010) return tuple3(0,4,6);
	    else if(buffertemp[7:0]  ==  8'b00000011) return tuple3(1,4,8);
	    else if(buffertemp[7:0]  ==  8'b00000010) return tuple3(2,4,8);
	    else if(buffertemp[7:1]  ==  7'b0000000) return tuple3(3,4,7);
	    else return tuple3(0,0,100);
	 end
      else if(nC[4] == 1 || nC[3] == 1)
	 begin
	    Bit#(6) buffertemp = inbuffer[buffersize-1:buffersize-6];
	    if(buffertemp[5:0]  ==  6'b000011) return tuple3(0,0,6);
	    else if(buffertemp[5:0]  ==  6'b000000) return tuple3(0,1,6);
	    else if(buffertemp[5:0]  ==  6'b000001) return tuple3(1,1,6);
	    else if(buffertemp[5:0]  ==  6'b000100) return tuple3(0,2,6);
	    else if(buffertemp[5:0]  ==  6'b000101) return tuple3(1,2,6);
	    else if(buffertemp[5:0]  ==  6'b000110) return tuple3(2,2,6);
	    else if(buffertemp[5:0]  ==  6'b001000) return tuple3(0,3,6);
	    else if(buffertemp[5:0]  ==  6'b001001) return tuple3(1,3,6);
	    else if(buffertemp[5:0]  ==  6'b001010) return tuple3(2,3,6);
	    else if(buffertemp[5:0]  ==  6'b001011) return tuple3(3,3,6);
	    else if(buffertemp[5:0]  ==  6'b001100) return tuple3(0,4,6);
	    else if(buffertemp[5:0]  ==  6'b001101) return tuple3(1,4,6);
	    else if(buffertemp[5:0]  ==  6'b001110) return tuple3(2,4,6);
	    else if(buffertemp[5:0]  ==  6'b001111) return tuple3(3,4,6);
	    else if(buffertemp[5:0]  ==  6'b010000) return tuple3(0,5,6);
	    else if(buffertemp[5:0]  ==  6'b010001) return tuple3(1,5,6);
	    else if(buffertemp[5:0]  ==  6'b010010) return tuple3(2,5,6);
	    else if(buffertemp[5:0]  ==  6'b010011) return tuple3(3,5,6);
	    else if(buffertemp[5:0]  ==  6'b010100) return tuple3(0,6,6);
	    else if(buffertemp[5:0]  ==  6'b010101) return tuple3(1,6,6);
	    else if(buffertemp[5:0]  ==  6'b010110) return tuple3(2,6,6);
	    else if(buffertemp[5:0]  ==  6'b010111) return tuple3(3,6,6);
	    else if(buffertemp[5:0]  ==  6'b011000) return tuple3(0,7,6);
	    else if(buffertemp[5:0]  ==  6'b011001) return tuple3(1,7,6);
	    else if(buffertemp[5:0]  ==  6'b011010) return tuple3(2,7,6);
	    else if(buffertemp[5:0]  ==  6'b011011) return tuple3(3,7,6);
	    else if(buffertemp[5:0]  ==  6'b011100) return tuple3(0,8,6);
	    else if(buffertemp[5:0]  ==  6'b011101) return tuple3(1,8,6);
	    else if(buffertemp[5:0]  ==  6'b011110) return tuple3(2,8,6);
	    else if(buffertemp[5:0]  ==  6'b011111) return tuple3(3,8,6);
	    else if(buffertemp[5:0]  ==  6'b100000) return tuple3(0,9,6);
	    else if(buffertemp[5:0]  ==  6'b100001) return tuple3(1,9,6);
	    else if(buffertemp[5:0]  ==  6'b100010) return tuple3(2,9,6);
	    else if(buffertemp[5:0]  ==  6'b100011) return tuple3(3,9,6);
	    else if(buffertemp[5:0]  ==  6'b100100) return tuple3(0,10,6);
	    else if(buffertemp[5:0]  ==  6'b100101) return tuple3(1,10,6);
	    else if(buffertemp[5:0]  ==  6'b100110) return tuple3(2,10,6);
	    else if(buffertemp[5:0]  ==  6'b100111) return tuple3(3,10,6);
	    else if(buffertemp[5:0]  ==  6'b101000) return tuple3(0,11,6);
	    else if(buffertemp[5:0]  ==  6'b101001) return tuple3(1,11,6);
	    else if(buffertemp[5:0]  ==  6'b101010) return tuple3(2,11,6);
	    else if(buffertemp[5:0]  ==  6'b101011) return tuple3(3,11,6);
	    else if(buffertemp[5:0]  ==  6'b101100) return tuple3(0,12,6);
	    else if(buffertemp[5:0]  ==  6'b101101) return tuple3(1,12,6);
	    else if(buffertemp[5:0]  ==  6'b101110) return tuple3(2,12,6);
	    else if(buffertemp[5:0]  ==  6'b101111) return tuple3(3,12,6);
	    else if(buffertemp[5:0]  ==  6'b110000) return tuple3(0,13,6);
	    else if(buffertemp[5:0]  ==  6'b110001) return tuple3(1,13,6);
	    else if(buffertemp[5:0]  ==  6'b110010) return tuple3(2,13,6);
	    else if(buffertemp[5:0]  ==  6'b110011) return tuple3(3,13,6);
	    else if(buffertemp[5:0]  ==  6'b110100) return tuple3(0,14,6);
	    else if(buffertemp[5:0]  ==  6'b110101) return tuple3(1,14,6);
	    else if(buffertemp[5:0]  ==  6'b110110) return tuple3(2,14,6);
	    else if(buffertemp[5:0]  ==  6'b110111) return tuple3(3,14,6);
	    else if(buffertemp[5:0]  ==  6'b111000) return tuple3(0,15,6);
	    else if(buffertemp[5:0]  ==  6'b111001) return tuple3(1,15,6);
	    else if(buffertemp[5:0]  ==  6'b111010) return tuple3(2,15,6);
	    else if(buffertemp[5:0]  ==  6'b111011) return tuple3(3,15,6);
	    else if(buffertemp[5:0]  ==  6'b111100) return tuple3(0,16,6);
	    else if(buffertemp[5:0]  ==  6'b111101) return tuple3(1,16,6);
	    else if(buffertemp[5:0]  ==  6'b111110) return tuple3(2,16,6);
	    else if(buffertemp[5:0]  ==  6'b111111) return tuple3(3,16,6);
	    else return tuple3(0,0,100);
	 end
      else if(nC[2] == 1)
	 begin
	    Bit#(10) buffertemp = inbuffer[buffersize-1:buffersize-10];
	    if(buffertemp[9:6]  ==  4'b1111) return tuple3(0,0,4);
	    else if(buffertemp[9:4]  ==  6'b001111) return tuple3(0,1,6);
	    else if(buffertemp[9:6]  ==  4'b1110) return tuple3(1,1,4);
	    else if(buffertemp[9:4]  ==  6'b001011) return tuple3(0,2,6);
	    else if(buffertemp[9:5]  ==  5'b01111) return tuple3(1,2,5);
	    else if(buffertemp[9:6]  ==  4'b1101) return tuple3(2,2,4);
	    else if(buffertemp[9:4]  ==  6'b001000) return tuple3(0,3,6);
	    else if(buffertemp[9:5]  ==  5'b01100) return tuple3(1,3,5);
	    else if(buffertemp[9:5]  ==  5'b01110) return tuple3(2,3,5);
	    else if(buffertemp[9:6]  ==  4'b1100) return tuple3(3,3,4);
	    else if(buffertemp[9:3]  ==  7'b0001111) return tuple3(0,4,7);
	    else if(buffertemp[9:5]  ==  5'b01010) return tuple3(1,4,5);
	    else if(buffertemp[9:5]  ==  5'b01011) return tuple3(2,4,5);
	    else if(buffertemp[9:6]  ==  4'b1011) return tuple3(3,4,4);
	    else if(buffertemp[9:3]  ==  7'b0001011) return tuple3(0,5,7);
	    else if(buffertemp[9:5]  ==  5'b01000) return tuple3(1,5,5);
	    else if(buffertemp[9:5]  ==  5'b01001) return tuple3(2,5,5);
	    else if(buffertemp[9:6]  ==  4'b1010) return tuple3(3,5,4);
	    else if(buffertemp[9:3]  ==  7'b0001001) return tuple3(0,6,7);
	    else if(buffertemp[9:4]  ==  6'b001110) return tuple3(1,6,6);
	    else if(buffertemp[9:4]  ==  6'b001101) return tuple3(2,6,6);
	    else if(buffertemp[9:6]  ==  4'b1001) return tuple3(3,6,4);
	    else if(buffertemp[9:3]  ==  7'b0001000) return tuple3(0,7,7);
	    else if(buffertemp[9:4]  ==  6'b001010) return tuple3(1,7,6);
	    else if(buffertemp[9:4]  ==  6'b001001) return tuple3(2,7,6);
	    else if(buffertemp[9:6]  ==  4'b1000) return tuple3(3,7,4);
	    else if(buffertemp[9:2]  ==  8'b00001111) return tuple3(0,8,8);
	    else if(buffertemp[9:3]  ==  7'b0001110) return tuple3(1,8,7);
	    else if(buffertemp[9:3]  ==  7'b0001101) return tuple3(2,8,7);
	    else if(buffertemp[9:5]  ==  5'b01101) return tuple3(3,8,5);
	    else if(buffertemp[9:2]  ==  8'b00001011) return tuple3(0,9,8);
	    else if(buffertemp[9:2]  ==  8'b00001110) return tuple3(1,9,8);
	    else if(buffertemp[9:3]  ==  7'b0001010) return tuple3(2,9,7);
	    else if(buffertemp[9:4]  ==  6'b001100) return tuple3(3,9,6);
	    else if(buffertemp[9:1]  ==  9'b000001111) return tuple3(0,10,9);
	    else if(buffertemp[9:2]  ==  8'b00001010) return tuple3(1,10,8);
	    else if(buffertemp[9:2]  ==  8'b00001101) return tuple3(2,10,8);
	    else if(buffertemp[9:3]  ==  7'b0001100) return tuple3(3,10,7);
	    else if(buffertemp[9:1]  ==  9'b000001011) return tuple3(0,11,9);
	    else if(buffertemp[9:1]  ==  9'b000001110) return tuple3(1,11,9);
	    else if(buffertemp[9:2]  ==  8'b00001001) return tuple3(2,11,8);
	    else if(buffertemp[9:2]  ==  8'b00001100) return tuple3(3,11,8);
	    else if(buffertemp[9:1]  ==  9'b000001000) return tuple3(0,12,9);
	    else if(buffertemp[9:1]  ==  9'b000001010) return tuple3(1,12,9);
	    else if(buffertemp[9:1]  ==  9'b000001101) return tuple3(2,12,9);
	    else if(buffertemp[9:2]  ==  8'b00001000) return tuple3(3,12,8);
	    else if(buffertemp[9:0]  == 10'b0000001101) return tuple3(0,13,10);
	    else if(buffertemp[9:1]  ==  9'b000000111) return tuple3(1,13,9);
	    else if(buffertemp[9:1]  ==  9'b000001001) return tuple3(2,13,9);
	    else if(buffertemp[9:1]  ==  9'b000001100) return tuple3(3,13,9);
	    else if(buffertemp[9:0]  == 10'b0000001001) return tuple3(0,14,10);
	    else if(buffertemp[9:0]  == 10'b0000001100) return tuple3(1,14,10);
	    else if(buffertemp[9:0]  == 10'b0000001011) return tuple3(2,14,10);
	    else if(buffertemp[9:0]  == 10'b0000001010) return tuple3(3,14,10);
	    else if(buffertemp[9:0]  == 10'b0000000101) return tuple3(0,15,10);
	    else if(buffertemp[9:0]  == 10'b0000001000) return tuple3(1,15,10);
	    else if(buffertemp[9:0]  == 10'b0000000111) return tuple3(2,15,10);
	    else if(buffertemp[9:0]  == 10'b0000000110) return tuple3(3,15,10);
	    else if(buffertemp[9:0]  == 10'b0000000001) return tuple3(0,16,10);
	    else if(buffertemp[9:0]  == 10'b0000000100) return tuple3(1,16,10);
	    else if(buffertemp[9:0]  == 10'b0000000011) return tuple3(2,16,10);
	    else if(buffertemp[9:0]  == 10'b0000000010) return tuple3(3,16,10);
	    else return tuple3(0,0,100);
	 end
      else if(nC[1] == 1)
	 begin
	    Bit#(14) buffertemp = inbuffer[buffersize-1:buffersize-14];
	    if(buffertemp[13:12] ==  2'b11) return tuple3(0,0,2);
	    else if(buffertemp[13:8]  ==  6'b001011) return tuple3(0,1,6);
	    else if(buffertemp[13:12] ==  2'b10) return tuple3(1,1,2);
	    else if(buffertemp[13:8]  ==  6'b000111) return tuple3(0,2,6);
	    else if(buffertemp[13:9]  ==  5'b00111) return tuple3(1,2,5);
	    else if(buffertemp[13:11] ==  3'b011) return tuple3(2,2,3);
	    else if(buffertemp[13:7]  ==  7'b0000111) return tuple3(0,3,7);
	    else if(buffertemp[13:8]  ==  6'b001010) return tuple3(1,3,6);
	    else if(buffertemp[13:8]  ==  6'b001001) return tuple3(2,3,6);
	    else if(buffertemp[13:10] ==  4'b0101) return tuple3(3,3,4);
	    else if(buffertemp[13:6]  ==  8'b00000111) return tuple3(0,4,8);
	    else if(buffertemp[13:8]  ==  6'b000110) return tuple3(1,4,6);
	    else if(buffertemp[13:8]  ==  6'b000101) return tuple3(2,4,6);
	    else if(buffertemp[13:10] ==  4'b0100) return tuple3(3,4,4);
	    else if(buffertemp[13:6]  ==  8'b00000100) return tuple3(0,5,8);
	    else if(buffertemp[13:7]  ==  7'b0000110) return tuple3(1,5,7);
	    else if(buffertemp[13:7]  ==  7'b0000101) return tuple3(2,5,7);
	    else if(buffertemp[13:9]  ==  5'b00110) return tuple3(3,5,5);
	    else if(buffertemp[13:5]  ==  9'b000000111) return tuple3(0,6,9);
	    else if(buffertemp[13:6]  ==  8'b00000110) return tuple3(1,6,8);
	    else if(buffertemp[13:6]  ==  8'b00000101) return tuple3(2,6,8);
	    else if(buffertemp[13:8]  ==  6'b001000) return tuple3(3,6,6);
	    else if(buffertemp[13:3]  == 11'b00000001111) return tuple3(0,7,11);
	    else if(buffertemp[13:5]  ==  9'b000000110) return tuple3(1,7,9);
	    else if(buffertemp[13:5]  ==  9'b000000101) return tuple3(2,7,9);
	    else if(buffertemp[13:8]  ==  6'b000100) return tuple3(3,7,6);
	    else if(buffertemp[13:3]  == 11'b00000001011) return tuple3(0,8,11);
	    else if(buffertemp[13:3]  == 11'b00000001110) return tuple3(1,8,11);
	    else if(buffertemp[13:3]  == 11'b00000001101) return tuple3(2,8,11);
	    else if(buffertemp[13:7]  ==  7'b0000100) return tuple3(3,8,7);
	    else if(buffertemp[13:2]  == 12'b000000001111) return tuple3(0,9,12);
	    else if(buffertemp[13:3]  == 11'b00000001010) return tuple3(1,9,11);
	    else if(buffertemp[13:3]  == 11'b00000001001) return tuple3(2,9,11);
	    else if(buffertemp[13:5]  ==  9'b000000100) return tuple3(3,9,9);
	    else if(buffertemp[13:2]  == 12'b000000001011) return tuple3(0,10,12);
	    else if(buffertemp[13:2]  == 12'b000000001110) return tuple3(1,10,12);
	    else if(buffertemp[13:2]  == 12'b000000001101) return tuple3(2,10,12);
	    else if(buffertemp[13:3]  == 11'b00000001100) return tuple3(3,10,11);
	    else if(buffertemp[13:2]  == 12'b000000001000) return tuple3(0,11,12);
	    else if(buffertemp[13:2]  == 12'b000000001010) return tuple3(1,11,12);
	    else if(buffertemp[13:2]  == 12'b000000001001) return tuple3(2,11,12);
	    else if(buffertemp[13:3]  == 11'b00000001000) return tuple3(3,11,11);
	    else if(buffertemp[13:1]  == 13'b0000000001111) return tuple3(0,12,13);
	    else if(buffertemp[13:1]  == 13'b0000000001110) return tuple3(1,12,13);
	    else if(buffertemp[13:1]  == 13'b0000000001101) return tuple3(2,12,13);
	    else if(buffertemp[13:2]  == 12'b000000001100) return tuple3(3,12,12);
	    else if(buffertemp[13:1]  == 13'b0000000001011) return tuple3(0,13,13);
	    else if(buffertemp[13:1]  == 13'b0000000001010) return tuple3(1,13,13);
	    else if(buffertemp[13:1]  == 13'b0000000001001) return tuple3(2,13,13);
	    else if(buffertemp[13:1]  == 13'b0000000001100) return tuple3(3,13,13);
	    else if(buffertemp[13:1]  == 13'b0000000000111) return tuple3(0,14,13);
	    else if(buffertemp[13:0]  == 14'b00000000001011) return tuple3(1,14,14);
	    else if(buffertemp[13:1]  == 13'b0000000000110) return tuple3(2,14,13);
	    else if(buffertemp[13:1]  == 13'b0000000001000) return tuple3(3,14,13);
	    else if(buffertemp[13:0]  == 14'b00000000001001) return tuple3(0,15,14);
	    else if(buffertemp[13:0]  == 14'b00000000001000) return tuple3(1,15,14);
	    else if(buffertemp[13:0]  == 14'b00000000001010) return tuple3(2,15,14);
	    else if(buffertemp[13:1]  == 13'b0000000000001) return tuple3(3,15,13);
	    else if(buffertemp[13:0]  == 14'b00000000000111) return tuple3(0,16,14);
	    else if(buffertemp[13:0]  == 14'b00000000000110) return tuple3(1,16,14);
	    else if(buffertemp[13:0]  == 14'b00000000000101) return tuple3(2,16,14);
	    else if(buffertemp[13:0]  == 14'b00000000000100) return tuple3(3,16,14);
	    else return tuple3(0,0,100);
	 end
      else
	 begin
	    Bit#(16) buffertemp = inbuffer[buffersize-1:buffersize-16];
	    if(buffertemp[15:15] ==  1'b1) return tuple3(0,0,1);
	    else if(buffertemp[15:10] ==  6'b000101) return tuple3(0,1,6);
	    else if(buffertemp[15:14] ==  2'b01) return tuple3(1,1,2);
	    else if(buffertemp[15:8]  ==  8'b00000111) return tuple3(0,2,8);
	    else if(buffertemp[15:10] ==  6'b000100) return tuple3(1,2,6);
	    else if(buffertemp[15:13] ==  3'b001) return tuple3(2,2,3);
	    else if(buffertemp[15:7]  ==  9'b000000111) return tuple3(0,3,9);
	    else if(buffertemp[15:8]  ==  8'b00000110) return tuple3(1,3,8);
	    else if(buffertemp[15:9]  ==  7'b0000101) return tuple3(2,3,7);
	    else if(buffertemp[15:11] ==  5'b00011) return tuple3(3,3,5);
	    else if(buffertemp[15:6]  == 10'b0000000111) return tuple3(0,4,10);
	    else if(buffertemp[15:7]  ==  9'b000000110) return tuple3(1,4,9);
	    else if(buffertemp[15:8]  ==  8'b00000101) return tuple3(2,4,8);
	    else if(buffertemp[15:10] ==  6'b000011) return tuple3(3,4,6);
	    else if(buffertemp[15:5]  == 11'b00000000111) return tuple3(0,5,11);
	    else if(buffertemp[15:6]  == 10'b0000000110) return tuple3(1,5,10);
	    else if(buffertemp[15:7]  ==  9'b000000101) return tuple3(2,5,9);
	    else if(buffertemp[15:9]  ==  7'b0000100) return tuple3(3,5,7);
	    else if(buffertemp[15:3]  == 13'b0000000001111) return tuple3(0,6,13);
	    else if(buffertemp[15:5]  == 11'b00000000110) return tuple3(1,6,11);
	    else if(buffertemp[15:6]  == 10'b0000000101) return tuple3(2,6,10);
	    else if(buffertemp[15:8]  ==  8'b00000100) return tuple3(3,6,8);
	    else if(buffertemp[15:3]  == 13'b0000000001011) return tuple3(0,7,13);
	    else if(buffertemp[15:3]  == 13'b0000000001110) return tuple3(1,7,13);
	    else if(buffertemp[15:5]  == 11'b00000000101) return tuple3(2,7,11);
	    else if(buffertemp[15:7]  ==  9'b000000100) return tuple3(3,7,9);
	    else if(buffertemp[15:3]  == 13'b0000000001000) return tuple3(0,8,13);
	    else if(buffertemp[15:3]  == 13'b0000000001010) return tuple3(1,8,13);
	    else if(buffertemp[15:3]  == 13'b0000000001101) return tuple3(2,8,13);
	    else if(buffertemp[15:6]  == 10'b0000000100) return tuple3(3,8,10);
	    else if(buffertemp[15:2]  == 14'b00000000001111) return tuple3(0,9,14);
	    else if(buffertemp[15:2]  == 14'b00000000001110) return tuple3(1,9,14);
	    else if(buffertemp[15:3]  == 13'b0000000001001) return tuple3(2,9,13);
	    else if(buffertemp[15:5]  == 11'b00000000100) return tuple3(3,9,11);
	    else if(buffertemp[15:2]  == 14'b00000000001011) return tuple3(0,10,14);
	    else if(buffertemp[15:2]  == 14'b00000000001010) return tuple3(1,10,14);
	    else if(buffertemp[15:2]  == 14'b00000000001101) return tuple3(2,10,14);
	    else if(buffertemp[15:3]  == 13'b0000000001100) return tuple3(3,10,13);
	    else if(buffertemp[15:1]  == 15'b000000000001111) return tuple3(0,11,15);
	    else if(buffertemp[15:1]  == 15'b000000000001110) return tuple3(1,11,15);
	    else if(buffertemp[15:2]  == 14'b00000000001001) return tuple3(2,11,14);
	    else if(buffertemp[15:2]  == 14'b00000000001100) return tuple3(3,11,14);
	    else if(buffertemp[15:1]  == 15'b000000000001011) return tuple3(0,12,15);
	    else if(buffertemp[15:1]  == 15'b000000000001010) return tuple3(1,12,15);
	    else if(buffertemp[15:1]  == 15'b000000000001101) return tuple3(2,12,15);
	    else if(buffertemp[15:2]  == 14'b00000000001000) return tuple3(3,12,14);
	    else if(buffertemp[15:0]  == 16'b0000000000001111) return tuple3(0,13,16);
	    else if(buffertemp[15:1]  == 15'b000000000000001) return tuple3(1,13,15);
	    else if(buffertemp[15:1]  == 15'b000000000001001) return tuple3(2,13,15);
	    else if(buffertemp[15:1]  == 15'b000000000001100) return tuple3(3,13,15);
	    else if(buffertemp[15:0]  == 16'b0000000000001011) return tuple3(0,14,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001110) return tuple3(1,14,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001101) return tuple3(2,14,16);
	    else if(buffertemp[15:1]  == 15'b000000000001000) return tuple3(3,14,15);
	    else if(buffertemp[15:0]  == 16'b0000000000000111) return tuple3(0,15,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001010) return tuple3(1,15,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001001) return tuple3(2,15,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001100) return tuple3(3,15,16);
	    else if(buffertemp[15:0]  == 16'b0000000000000100) return tuple3(0,16,16);
	    else if(buffertemp[15:0]  == 16'b0000000000000110) return tuple3(1,16,16);
	    else if(buffertemp[15:0]  == 16'b0000000000000101) return tuple3(2,16,16);
	    else if(buffertemp[15:0]  == 16'b0000000000001000) return tuple3(3,16,16);
	    else return tuple3(0,0,100);
	 end
   endfunction
   
   (* noinline *)
   function Bit#(4) cavlc_level_prefix( Buffer inbuffer );
      Bit#(4) tempout = 15;
      for(Integer ii=15; ii>0; ii=ii-1)
	 begin
	    if(inbuffer[buffersize-fromInteger(ii)]==1'b1)
	       tempout = fromInteger(ii)-1;
	 end
      return tempout;
   endfunction

   (* noinline *)
   function Tuple2#(Bit#(4),Bufcount) cavlc_total_zeros( Buffer inbuffer, Bit#(4) inTotalCoeff, Bit#(5) inMaxNumCoeff);
      if(inMaxNumCoeff==4)
	 begin
	    Bit#(3) buffertemp3 = inbuffer[buffersize-1:buffersize-3];
	    Bit#(2) buffertemp2 = inbuffer[buffersize-1:buffersize-2];
	    case ( inTotalCoeff )
	       1:
	       begin
		  if(inbuffer[buffersize-1] == 1)
		     return tuple2(0,1);
		  else if(buffertemp2 == 2'b01)
		     return tuple2(1,2);
		  else if(buffertemp3 == 3'b001)
		     return tuple2(2,3);
		  else
		     return tuple2(3,3);
	       end
	       2:
	       begin
		  if(inbuffer[buffersize-1] == 1)
		     return tuple2(0,1);
		  else if(buffertemp2 == 2'b01)
		     return tuple2(1,2);
		  else
		     return tuple2(2,2);
	       end
	       3:
	       begin
		  if(inbuffer[buffersize-1] == 1)
		     return tuple2(0,1);
		  else
		     return tuple2(1,1);
	       end
	       default: return tuple2(0,100);
	    endcase
	 end
      else
	 begin
	    Bit#(6) buffertemp = inbuffer[buffersize-1:buffersize-6];
	    case ( inTotalCoeff )
	       1:
	       begin
		  Bit#(10) buffertemp2 = inbuffer[buffersize-1:buffersize-10];
		  if(buffertemp2[9:9]  ==  1'b1) return tuple2(0,1);
		  else if(buffertemp2[9:7]  ==  3'b011) return tuple2(1,3);
		  else if(buffertemp2[9:7]  ==  3'b010) return tuple2(2,3);
		  else if(buffertemp2[9:6]  ==  4'b0011) return tuple2(3,4);
		  else if(buffertemp2[9:6]  ==  4'b0010) return tuple2(4,4);
		  else if(buffertemp2[9:5]  ==  5'b00011) return tuple2(5,5);
		  else if(buffertemp2[9:5]  ==  5'b00010) return tuple2(6,5);
		  else if(buffertemp2[9:4]  ==  6'b000011) return tuple2(7,6);
		  else if(buffertemp2[9:4]  ==  6'b000010) return tuple2(8,6);
		  else if(buffertemp2[9:3]  ==  7'b0000011) return tuple2(9,7);
		  else if(buffertemp2[9:3]  ==  7'b0000010) return tuple2(10,7);
		  else if(buffertemp2[9:2]  ==  8'b00000011) return tuple2(11,8);
		  else if(buffertemp2[9:2]  ==  8'b00000010) return tuple2(12,8);
		  else if(buffertemp2[9:1]  ==  9'b000000011) return tuple2(13,9);
		  else if(buffertemp2[9:1]  ==  9'b000000010) return tuple2(14,9);
		  else return tuple2(15,9);
	       end
	       2:
	       begin
		  if(buffertemp[5:3]  ==  3'b111) return tuple2(0,3);
		  else if(buffertemp[5:3]  ==  3'b110) return tuple2(1,3);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(2,3);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(3,3);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(4,3);
		  else if(buffertemp[5:2]  ==  4'b0101) return tuple2(5,4);
		  else if(buffertemp[5:2]  ==  4'b0100) return tuple2(6,4);
		  else if(buffertemp[5:2]  ==  4'b0011) return tuple2(7,4);
		  else if(buffertemp[5:2]  ==  4'b0010) return tuple2(8,4);
		  else if(buffertemp[5:1]  ==  5'b00011) return tuple2(9,5);
		  else if(buffertemp[5:1]  ==  5'b00010) return tuple2(10,5);
		  else if(buffertemp[5:0]  ==  6'b000011) return tuple2(11,6);
		  else if(buffertemp[5:0]  ==  6'b000010) return tuple2(12,6);
		  else if(buffertemp[5:0]  ==  6'b000001) return tuple2(13,6);
		  else return tuple2(14,6);
	       end
	       3:
	       begin
		  if(buffertemp[5:2]  ==  4'b0101) return tuple2(0,4);
		  else if(buffertemp[5:3]  ==  3'b111) return tuple2(1,3);
		  else if(buffertemp[5:3]  ==  3'b110) return tuple2(2,3);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(3,3);
		  else if(buffertemp[5:2]  ==  4'b0100) return tuple2(4,4);
		  else if(buffertemp[5:2]  ==  4'b0011) return tuple2(5,4);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(6,3);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(7,3);
		  else if(buffertemp[5:2]  ==  4'b0010) return tuple2(8,4);
		  else if(buffertemp[5:1]  ==  5'b00011) return tuple2(9,5);
		  else if(buffertemp[5:1]  ==  5'b00010) return tuple2(10,5);
		  else if(buffertemp[5:0]  ==  6'b000001) return tuple2(11,6);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(12,5);
		  else return tuple2(13,6);
	       end
	       4:
	       begin
		  if(buffertemp[5:1]  ==  5'b00011) return tuple2(0,5);
		  else if(buffertemp[5:3]  ==  3'b111) return tuple2(1,3);
		  else if(buffertemp[5:2]  ==  4'b0101) return tuple2(2,4);
		  else if(buffertemp[5:2]  ==  4'b0100) return tuple2(3,4);
		  else if(buffertemp[5:3]  ==  3'b110) return tuple2(4,3);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(5,3);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(6,3);
		  else if(buffertemp[5:2]  ==  4'b0011) return tuple2(7,4);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(8,3);
		  else if(buffertemp[5:2]  ==  4'b0010) return tuple2(9,4);
		  else if(buffertemp[5:1]  ==  5'b00010) return tuple2(10,5);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(11,5);
		  else return tuple2(12,5);
	       end
	       5:
	       begin
		  if(buffertemp[5:2]  ==  4'b0101) return tuple2(0,4);
		  else if(buffertemp[5:2]  ==  4'b0100) return tuple2(1,4);
		  else if(buffertemp[5:2]  ==  4'b0011) return tuple2(2,4);
		  else if(buffertemp[5:3]  ==  3'b111) return tuple2(3,3);
		  else if(buffertemp[5:3]  ==  3'b110) return tuple2(4,3);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(5,3);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(6,3);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(7,3);
		  else if(buffertemp[5:2]  ==  4'b0010) return tuple2(8,4);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(9,5);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(10,4);
		  else return tuple2(11,5);
	       end
	       6:
	       begin
		  if(buffertemp[5:0]  ==  6'b000001) return tuple2(0,6);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(1,5);
		  else if(buffertemp[5:3]  ==  3'b111) return tuple2(2,3);
		  else if(buffertemp[5:3]  ==  3'b110) return tuple2(3,3);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(4,3);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(5,3);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(6,3);
		  else if(buffertemp[5:3]  ==  3'b010) return tuple2(7,3);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(8,4);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(9,3);
		  else return tuple2(10,6);
	       end
	       7:
	       begin
		  if(buffertemp[5:0]  ==  6'b000001) return tuple2(0,6);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(1,5);
		  else if(buffertemp[5:3]  ==  3'b101) return tuple2(2,3);
		  else if(buffertemp[5:3]  ==  3'b100) return tuple2(3,3);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(4,3);
		  else if(buffertemp[5:4]  ==  2'b11) return tuple2(5,2);
		  else if(buffertemp[5:3]  ==  3'b010) return tuple2(6,3);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(7,4);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(8,3);
		  else return tuple2(9,6);
	       end
	       8:
	       begin
		  if(buffertemp[5:0]  ==  6'b000001) return tuple2(0,6);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(1,4);
		  else if(buffertemp[5:1]  ==  5'b00001) return tuple2(2,5);
		  else if(buffertemp[5:3]  ==  3'b011) return tuple2(3,3);
		  else if(buffertemp[5:4]  ==  2'b11) return tuple2(4,2);
		  else if(buffertemp[5:4]  ==  2'b10) return tuple2(5,2);
		  else if(buffertemp[5:3]  ==  3'b010) return tuple2(6,3);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(7,3);
		  else return tuple2(8,6);
	       end
	       9:
	       begin
		  if(buffertemp[5:0]  ==  6'b000001) return tuple2(0,6);
		  else if(buffertemp[5:0]  ==  6'b000000) return tuple2(1,6);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(2,4);
		  else if(buffertemp[5:4]  ==  2'b11) return tuple2(3,2);
		  else if(buffertemp[5:4]  ==  2'b10) return tuple2(4,2);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(5,3);
		  else if(buffertemp[5:4]  ==  2'b01) return tuple2(6,2);
		  else return tuple2(7,5);
	       end
	       10:
	       begin
		  if(buffertemp[5:1]  ==  5'b00001) return tuple2(0,5);
		  else if(buffertemp[5:1]  ==  5'b00000) return tuple2(1,5);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(2,3);
		  else if(buffertemp[5:4]  ==  2'b11) return tuple2(3,2);
		  else if(buffertemp[5:4]  ==  2'b10) return tuple2(4,2);
		  else if(buffertemp[5:4]  ==  2'b01) return tuple2(5,2);
		  else return tuple2(6,4);
	       end
	       11:
	       begin
		  if(buffertemp[5:2]  ==  4'b0000) return tuple2(0,4);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(1,4);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(2,3);
		  else if(buffertemp[5:3]  ==  3'b010) return tuple2(3,3);
		  else if(buffertemp[5:5]  ==  1'b1) return tuple2(4,1);
		  else return tuple2(5,3);
	       end
	       12:
	       begin
		  if(buffertemp[5:2]  ==  4'b0000) return tuple2(0,4);
		  else if(buffertemp[5:2]  ==  4'b0001) return tuple2(1,4);
		  else if(buffertemp[5:4]  ==  2'b01) return tuple2(2,2);
		  else if(buffertemp[5:5]  ==  1'b1) return tuple2(3,1);
		  else return tuple2(4,3);
	       end
	       13:
	       begin
		  if(buffertemp[5:3]  ==  3'b000) return tuple2(0,3);
		  else if(buffertemp[5:3]  ==  3'b001) return tuple2(1,3);
		  else if(buffertemp[5:5]  ==  1'b1) return tuple2(2,1);
		  else return tuple2(3,2);
	       end
	       14:
	       begin
		  if(buffertemp[5:4]  ==  2'b00) return tuple2(0,2);
		  else if(buffertemp[5:4]  ==  2'b01) return tuple2(1,2);
		  else return tuple2(2,1);
	       end
	       15:
	       begin
		  if(buffertemp[5:5]  ==  1'b0) return tuple2(0,1);
		  else return tuple2(1,1);
	       end
               default: return tuple2(0,100);
	    endcase
	 end
   endfunction

   (* noinline *)
   function Tuple2#(Bit#(4),Bufcount) cavlc_run_before( Buffer inbuffer, Bit#(4) inZerosLeft);
      Bit#(3) buffertemp3 = inbuffer[buffersize-1:buffersize-3];
      Bit#(2) buffertemp2 = inbuffer[buffersize-1:buffersize-2];
      case ( inZerosLeft )
	 0: return tuple2(0,100);
	 1:
	 begin
	    if(inbuffer[buffersize-1] == 1)
	       return tuple2(0,1);
	    else
	       return tuple2(1,1);
	 end
	 2:
	 begin
	    if(inbuffer[buffersize-1] == 1)
	       return tuple2(0,1);
	    else if(buffertemp2 == 2'b01)
	       return tuple2(1,2);
	    else
	       return tuple2(2,2);
	 end
	 3:
	 begin
	    if(buffertemp2 == 2'b11)
	       return tuple2(0,2);
	    else if(buffertemp2 == 2'b10)
	       return tuple2(1,2);
	    else if(buffertemp2 == 2'b01)
	       return tuple2(2,2);
	    else
	       return tuple2(3,2);
	 end
	 4:
	 begin
	    if(buffertemp2 == 2'b11)
	       return tuple2(0,2);
	    else if(buffertemp2 == 2'b10)
	       return tuple2(1,2);
	    else if(buffertemp2 == 2'b01)
	       return tuple2(2,2);
	    else if(buffertemp3 == 3'b001)
	       return tuple2(3,3);
	    else
	       return tuple2(4,3);
	 end
	 5:
	 begin
	    if(buffertemp2 == 2'b11)
	       return tuple2(0,2);
	    else if(buffertemp2 == 2'b10)
	       return tuple2(1,2);
	    else if(buffertemp3 == 3'b011)
	       return tuple2(2,3);
	    else if(buffertemp3 == 3'b010)
	       return tuple2(3,3);
	    else if(buffertemp3 == 3'b001)
	       return tuple2(4,3);
	    else
	       return tuple2(5,3);
	 end
	 6:
	 begin
	    if(buffertemp2 == 2'b11)
	       return tuple2(0,2);
	    else if(buffertemp3 == 3'b000)
	       return tuple2(1,3);
	    else if(buffertemp3 == 3'b001)
	       return tuple2(2,3);
	    else if(buffertemp3 == 3'b011)
	       return tuple2(3,3);
	    else if(buffertemp3 == 3'b010)
	       return tuple2(4,3);
	    else if(buffertemp3 == 3'b101)
	       return tuple2(5,3);
	    else
	       return tuple2(6,3);
	 end
	 default:
	 begin
	    if(buffertemp3 != 3'b000)
	       begin
		  Bit#(4) outputtemp = zeroExtend(3'b111 - buffertemp3);
		  return tuple2(outputtemp,3);
	       end
	    else
	       begin
		  Bit#(4) returnVal1 = 14;
		  Bufcount returnVal2 = 11;
		  for(Integer ii=10; ii>=4; ii=ii-1)
		     begin
			if(inbuffer[buffersize-fromInteger(ii)]==1'b1)
			   begin
			      returnVal1 = fromInteger(ii)+3;
			      returnVal2 = fromInteger(ii);
			   end
		     end
		  return tuple2(returnVal1,returnVal2);
	       end
	 end
      endcase
   endfunction



endpackage
