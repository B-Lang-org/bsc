/////////////////////////////////////////////////////////////////////////
/* Performs byte alignment on a 8 bit input data and returns 8 bit data 
   and stores the residual value in input buffer 
*/

package DetstartCode;

/*
interface DetstartCode_IFC;
  method Tuple3#(Bool,Bit#(4)) detvideoobjectstartcode(Bit#(40) input_reg, Bit#(4) pos ,VideoSt state;
endinterface: DetstartCode_IFC
*/

function Tuple3#(Bool,Bit#(4),Bit#(5)) detvideoobjectstartcode (Bit#(40) input_reg);
Tuple3#(Bool,Bit#(4),Bit#(5)) res;
   if (input_reg[31:5] == 27'h0008)
	   res = tuple3(True,0,input_reg[4:0]);
   else if (input_reg[32:6] == 27'h0008)
	   res = tuple3(True,1,input_reg[5:1]);
   else if (input_reg[33:7] == 27'h0008)
	   res = tuple3(True,2,input_reg[6:2]);
   else if (input_reg[34:8] == 27'h0008)
	   res = tuple3(True,3,input_reg[7:3]);
   else if (input_reg[35:9] == 27'h0008)
	   res = tuple3(True,4,input_reg[8:4]);
   else if (input_reg[36:10] == 27'h0008)
	   res = tuple3(True,5,input_reg[9:5]);
   else if (input_reg[37:11] == 27'h0008)
	   res = tuple3(True,6,input_reg[10:6]);
   else if (input_reg[38:12] == 27'h0008)
	   res = tuple3(True,7,input_reg[11:7]);
   else
	   res = tuple3(False,0,input_reg[4:0]);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(8)) detstartcode (Bit#(40) input_reg);
Tuple3#(Bool,Bit#(4),Bit#(8)) res;
   if (input_reg[31:8] == 24'h00001)
	   res = tuple3(True,0,input_reg[7:0]);
   else if (input_reg[32:9] == 24'h00001)
	   res = tuple3(True,1,input_reg[8:1]);
   else if (input_reg[33:10] == 24'h00001)
	   res = tuple3(True,2,input_reg[9:2]);
   else if (input_reg[34:11] == 24'h00001)
	   res = tuple3(True,3,input_reg[10:3]);
   else if (input_reg[35:12] == 24'h00001)
	   res = tuple3(True,4,input_reg[11:4]);
   else if (input_reg[36:13] == 24'h00001)
	   res = tuple3(True,5,input_reg[12:5]);
   else if (input_reg[37:14] == 24'h00001)
	   res = tuple3(True,6,input_reg[13:6]);
   else if (input_reg[38:15] == 24'h00001)
	   res = tuple3(True,7,input_reg[14:7]);
   else
	   res = tuple3(False,0,input_reg[7:0]);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(4)) detvideoobjectlayerstartcode (Bit#(40) input_reg);
Tuple3#(Bool,Bit#(4),Bit#(4)) res;
   if (input_reg[31:4] == 28'h0012)
	   res = tuple3(True,0,input_reg[3:0]);
   else if (input_reg[32:5] == 28'h0012)
	   res = tuple3(True,1,input_reg[4:1]);
   else if (input_reg[33:6] == 28'h0012)
	   res = tuple3(True,2,input_reg[5:2]);
   else if (input_reg[34:7] == 28'h0012)
	   res = tuple3(True,3,input_reg[6:3]);
   else if (input_reg[35:8] == 28'h0012)
	   res = tuple3(True,4,input_reg[7:4]);
   else if (input_reg[36:9] == 28'h0012)
	   res = tuple3(True,5,input_reg[8:5]);
   else if (input_reg[37:10] == 28'h0012)
	   res = tuple3(True,6,input_reg[9:6]);
   else if (input_reg[38:11] == 28'h0012)
	   res = tuple3(True,7,input_reg[10:7]);
   else
	   res = tuple3(False,0,input_reg[3:0]);
   return res;
endfunction

function Tuple3#(Bit#(3),Bit#(2),Bit#(5)) decode_mcbpcI (Bit#(9) input_reg);
Tuple3#(Bit#(3),Bit#(2),Bit#(5)) res;
   if (input_reg[8] == 1)
     res = tuple3(3,0,1);
   else if (input_reg[8:6] == 3'b001)
     res = tuple3(3,1,3);
   else if (input_reg[8:6] == 3'b010)
     res = tuple3(3,2,3);
   else if (input_reg[8:6] == 3'b011)
     res = tuple3(3,3,3);
   else if (input_reg[8:5] == 4'b0001)
     res = tuple3(4,0,4);
   else if (input_reg[8:3] == 6'b000001)
     res = tuple3(4,1,6);
   else if (input_reg[8:3] == 6'b000010)
     res = tuple3(4,2,6);
   else if (input_reg[8:3] == 6'b000011)
     res = tuple3(4,3,6);
   else if (input_reg[8:0] == 9'b000000001)
     res = tuple3(7,0,9);
   else
     res = tuple3(0,0,0);
   return res;
endfunction

function Tuple3#(Bit#(3),Bit#(2),Bit#(5)) decode_mcbpcP (Bit#(9) input_reg);
Tuple3#(Bit#(3),Bit#(2),Bit#(5)) res;
   if (input_reg[8] == 1)
     res = tuple3(0,0,1);
   else if (input_reg[8:6] == 3'b011)
     res = tuple3(1,0,3);
   else if (input_reg[8:6] == 3'b010)
     res = tuple3(2,0,3);
   else if (input_reg[8:5] == 4'b0011)
     res = tuple3(0,1,4);
   else if (input_reg[8:5] == 4'b0010)
     res = tuple3(0,2,4);
   else if (input_reg[8:4] == 5'b00011)
     res = tuple3(3,0,5);
   else if (input_reg[8:3] == 6'b000101)
     res = tuple3(0,3,6);
   else if (input_reg[8:3] == 6'b000100)
     res = tuple3(4,0,6);
   else if (input_reg[8:2] == 7'b0000111)
     res = tuple3(1,1,7);
   else if (input_reg[8:2] == 7'b0000110)
     res = tuple3(1,2,7);
   else if (input_reg[8:2] == 7'b0000101)
     res = tuple3(2,1,7);
   else if (input_reg[8:2] == 7'b0000100)
     res = tuple3(2,2,7);
   else if (input_reg[8:2] == 7'b0000011)
     res = tuple3(3,3,7);
   else if (input_reg[8:1] == 8'b00000101)
     res = tuple3(2,3,8);
   else if (input_reg[8:1] == 8'b00000100)
     res = tuple3(3,1,8);
   else if (input_reg[8:1] == 8'b00000011)
     res = tuple3(3,2,8);
   else if (input_reg[8:0] == 9'b000000101)
     res = tuple3(1,3,9);
   else if (input_reg[8:0] == 9'b000000100)
     res = tuple3(4,1,9);
   else if (input_reg[8:0] == 9'b000000011)
     res = tuple3(4,2,9);
   else if (input_reg[8:0] == 9'b000000010)
     res = tuple3(4,3,9);
   else if (input_reg[8:0] == 9'b000000001)
     res = tuple3(7,0,9);
   else
     res = tuple3(0,0,0);
   return res;
endfunction

function Tuple2#(Bit#(4),Bit#(5)) decode_cbpyI (Bit#(6) input_reg);
Tuple2#(Bit#(4),Bit#(5)) res;
   if (input_reg[5:4] == 2'b11)
     res = tuple2(4'b1111,2);
   else if (input_reg[5:2] == 4'b0011)
     res = tuple2(4'b0000,4);
   else if (input_reg[5:2] == 4'b1001)
     res = tuple2(4'b0011,4);
   else if (input_reg[5:2] == 4'b0111)
     res = tuple2(4'b0101,4);
   else if (input_reg[5:2] == 4'b1011)
     res = tuple2(4'b0111,4);
   else if (input_reg[5:2] == 4'b0101)
     res = tuple2(4'b1010,4);
   else if (input_reg[5:2] == 4'b1010)
     res = tuple2(4'b1011,4);
   else if (input_reg[5:2] == 4'b0100)
     res = tuple2(4'b1100,4);
   else if (input_reg[5:2] == 4'b1000)
     res = tuple2(4'b1101,4);
   else if (input_reg[5:2] == 4'b0110)
     res = tuple2(4'b1110,4);
   else if (input_reg[5:1] == 5'b00101)
     res = tuple2(4'b0001,5);
   else if (input_reg[5:1] == 5'b00100)
     res = tuple2(4'b0010,5);
   else if (input_reg[5:1] == 5'b00011)
     res = tuple2(4'b0100,5);
   else if (input_reg[5:1] == 5'b00010)
     res = tuple2(4'b1000,5);
   else if (input_reg[5:0] == 6'b000010)
     res = tuple2(4'b0110,6);
   else if (input_reg[5:0] == 6'b000011)
     res = tuple2(4'b1001,6);
   else
     res = tuple2(0,0);
   return res;
endfunction

function Tuple2#(Bit#(4),Bit#(5)) decode_cbpyP (Bit#(6) input_reg);
Tuple2#(Bit#(4),Bit#(5)) res;
   if (input_reg[5:4] == 2'b11)
     res = tuple2(4'b0000,2);
   else if (input_reg[5:2] == 4'b0011)
     res = tuple2(4'b1111,4);
   else if (input_reg[5:2] == 4'b1001)
     res = tuple2(4'b1100,4);
   else if (input_reg[5:2] == 4'b0111)
     res = tuple2(4'b1010,4);
   else if (input_reg[5:2] == 4'b1011)
     res = tuple2(4'b1000,4);
   else if (input_reg[5:2] == 4'b0101)
     res = tuple2(4'b0101,4);
   else if (input_reg[5:2] == 4'b1010)
     res = tuple2(4'b0100,4);
   else if (input_reg[5:2] == 4'b0100)
     res = tuple2(4'b0011,4);
   else if (input_reg[5:2] == 4'b1000)
     res = tuple2(4'b0010,4);
   else if (input_reg[5:2] == 4'b0110)
     res = tuple2(4'b0001,4);
   else if (input_reg[5:1] == 5'b00101)
     res = tuple2(4'b1110,5);
   else if (input_reg[5:1] == 5'b00100)
     res = tuple2(4'b1101,5);
   else if (input_reg[5:1] == 5'b00011)
     res = tuple2(4'b1011,5);
   else if (input_reg[5:1] == 5'b00010)
     res = tuple2(4'b0111,5);
   else if (input_reg[5:0] == 6'b000010)
     res = tuple2(4'b1001,6);
   else if (input_reg[5:0] == 6'b000011)
     res = tuple2(4'b0110,6);
   else
     res = tuple2(0,0);
   return res;
endfunction

function Tuple3#(Bool,Bit#(12),Bit#(5)) decode_MV4 (Bit#(5) input_reg);
   Tuple3#(Bool,Bit#(12),Bit#(5)) res;
   if (input_reg[4] == 1)
     res = tuple3(True,12'd0,1);
   else if (input_reg[4:2] == 3'b010)
     res = tuple3(True,12'd1,3);
   else if (input_reg[4:2] == 3'b011)
     res = tuple3(True,12'hfff,3);
   else if (input_reg[4:1] == 4'b0010)
     res = tuple3(True,12'h002,4);
   else if (input_reg[4:1] == 4'b0011)
     res = tuple3(True,12'hffe,4);
   else if (input_reg[4:0] == 5'b00010)
     res = tuple3(True,12'h003,5);
   else if (input_reg[4:0] == 5'b00011)
     res = tuple3(True,12'hffd,5);
   else
     res = tuple3(False,12'h000,4);
   return res;
endfunction

function Tuple3#(Bool,Bit#(12),Bit#(5)) decode_MV7 (Bit#(7) input_reg);
   Tuple3#(Bool,Bit#(12),Bit#(5)) res;
   if (input_reg[6:4] == 3'b110)
     res = tuple3(True,12'h004,3);
   else if (input_reg[6:3] == 4'b1010)
     res = tuple3(True,12'h005,4);
   else if (input_reg[6:3] == 4'b1000)
     res = tuple3(True,12'h006,4);
   else if (input_reg[6:3] == 4'b0110)
     res = tuple3(True,12'h007,4);
   else if (input_reg[6:3] == 4'b0110)
     res = tuple3(True,12'h007,4);
   else if (input_reg[6:1] == 6'b010110)
     res = tuple3(True,12'h008,6);
   else if (input_reg[6:1] == 6'b010100)
     res = tuple3(True,12'h009,6);
   else if (input_reg[6:1] == 6'b010010)
     res = tuple3(True,12'h00a,6);
   else if (input_reg[6:0] == 7'b0100010)
     res = tuple3(True,12'h00b,7);
   else if (input_reg[6:0] == 7'b0100000)
     res = tuple3(True,12'h00c,7);
   else if (input_reg[6:0] == 7'b0011110)
     res = tuple3(True,12'h00d,7);
   else if (input_reg[6:0] == 7'b0011100)
     res = tuple3(True,12'h00e,7);
   else if (input_reg[6:0] == 7'b0011010)
     res = tuple3(True,12'h00f,7);
   else if (input_reg[6:0] == 7'b0011000)
     res = tuple3(True,12'h010,7);
   else if (input_reg[6:0] == 7'b0010110)
     res = tuple3(True,12'h011,7);
   else if (input_reg[6:0] == 7'b0010100)
     res = tuple3(True,12'h012,7);
   else if (input_reg[6:0] == 7'b0010010)
     res = tuple3(True,12'h013,7);
   else if (input_reg[6:0] == 7'b0010000)
     res = tuple3(True,12'h014,7);
   else if (input_reg[6:0] == 7'b0001110)
     res = tuple3(True,12'h015,7);
   else if (input_reg[6:0] == 7'b0001100)
     res = tuple3(True,12'h016,7);
   else if (input_reg[6:0] == 7'b0001010)
     res = tuple3(True,12'h017,7);
   else if (input_reg[6:0] == 7'b0001000)
     res = tuple3(True,12'h018,7);
   else if (input_reg[6:4] == 3'b111)
     res = tuple3(True,12'hffc,3);
   else if (input_reg[6:3] == 4'b1011)
     res = tuple3(True,12'hffb,4);
   else if (input_reg[6:3] == 4'b1001)
     res = tuple3(True,12'hffa,4);
   else if (input_reg[6:3] == 4'b0111)
     res = tuple3(True,12'hff9,4);
   else if (input_reg[6:1] == 6'b010111)
     res = tuple3(True,12'hff8,6);
   else if (input_reg[6:1] == 6'b010101)
     res = tuple3(True,12'hff7,6);
   else if (input_reg[6:1] == 6'b010011)
     res = tuple3(True,12'hff6,6);
   else if (input_reg[6:0] == 7'b0100011)
     res = tuple3(True,12'hff5,7);
   else if (input_reg[6:0] == 7'b0100001)
     res = tuple3(True,12'hff4,7);
   else if (input_reg[6:0] == 7'b0011111)
     res = tuple3(True,12'hff3,7);
   else if (input_reg[6:0] == 7'b0011101)
     res = tuple3(True,12'hff2,7);
   else if (input_reg[6:0] == 7'b0011011)
     res = tuple3(True,12'hff1,7);
   else if (input_reg[6:0] == 7'b0011001)
     res = tuple3(True,12'hff0,7);
   else if (input_reg[6:0] == 7'b0010111)
     res = tuple3(True,12'hfef,7);
   else if (input_reg[6:0] == 7'b0010101)
     res = tuple3(True,12'hfee,7);
   else if (input_reg[6:0] == 7'b0010011)
     res = tuple3(True,12'hfed,7);
   else if (input_reg[6:0] == 7'b0010001)
     res = tuple3(True,12'hfec,7);
   else if (input_reg[6:0] == 7'b0001111)
     res = tuple3(True,12'hfeb,7);
   else if (input_reg[6:0] == 7'b0001101)
     res = tuple3(True,12'hfea,7);
   else if (input_reg[6:0] == 7'b0001011)
     res = tuple3(True,12'hfe9,7);
   else if (input_reg[6:0] == 7'b0001001)
     res = tuple3(True,12'hfe8,7);
   else
     res = tuple3(False,12'h000,4);
   return res;
endfunction

function Tuple3#(Bool,Bit#(12),Bit#(5)) decode_MV5 (Bit#(5) input_reg);
   Tuple3#(Bool,Bit#(12),Bit#(5)) res;
   if (input_reg[4:1] == 4'b1110)
     res = tuple3(True,12'h019,4);
   else if (input_reg[4:1] == 4'b1100)
     res = tuple3(True,12'h01a,4);
   else if (input_reg[4:1] == 4'b1010)
     res = tuple3(True,12'h01b,4);
   else if (input_reg[4:1] == 4'b1000)
     res = tuple3(True,12'h01c,4);
   else if (input_reg[4:1] == 4'b0110)
     res = tuple3(True,12'h01d,4);
   else if (input_reg[4:1] == 4'b0100)
     res = tuple3(True,12'h01e,4);
   else if (input_reg[4:0] == 5'b00110)
     res = tuple3(True,12'h01f,5);
   else if (input_reg[4:0] == 5'b00100)
     res = tuple3(True,12'h020,5);
   else if (input_reg[4:1] == 4'b1111)
     res = tuple3(True,12'hfe7,4);
   else if (input_reg[4:1] == 4'b1101)
     res = tuple3(True,12'hfe6,4);
   else if (input_reg[4:1] == 4'b1011)
     res = tuple3(True,12'hfe5,4);
   else if (input_reg[4:1] == 4'b1001)
     res = tuple3(True,12'hfe4,4);
   else if (input_reg[4:1] == 4'b0111)
     res = tuple3(True,12'hfe3,4);
   else if (input_reg[4:1] == 4'b0101)
     res = tuple3(True,12'hfe2,4);
   else if (input_reg[4:0] == 5'b00111)
     res = tuple3(True,12'hfe1,5);
   else if (input_reg[4:0] == 5'b00101)
     res = tuple3(True,12'hfe0,5);
   else
     res = tuple3(False,12'h000,4);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(5)) decode_dct_dc_size_luma4 (Bit#(4) input_reg);
   Tuple3#(Bool,Bit#(4),Bit#(5)) res;
   if (input_reg[3:1] == 3'b011)
     res = tuple3(True,4'd0,3);
   else if (input_reg[3:2] == 2'b11)
     res = tuple3(True,4'd1,2);
   else if (input_reg[3:2] == 2'b10)
     res = tuple3(True,4'd2,2);
   else if (input_reg[3:1] == 3'b010)
     res = tuple3(True,4'd3,3);
   else if (input_reg[3:1] == 3'b001)
     res = tuple3(True,4'd4,3);
   else if (input_reg[3:0] == 4'b0001)
     res = tuple3(True,4'd5,4);
   else
     res = tuple3(False,4'd0,4);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(5)) decode_dct_dc_size_luma7 (Bit#(7) input_reg);
   Tuple3#(Bool,Bit#(4),Bit#(5)) res;
   if (input_reg[6] == 1)
     res = tuple3(True,4'd6,1);
   else if (input_reg[6:5] == 2'b01)
     res = tuple3(True,4'd7,2);
   else if (input_reg[6:4] == 3'b001)
     res = tuple3(True,4'd8,3);
   else if (input_reg[6:3] == 4'b0001)
     res = tuple3(True,4'd9,4);
   else if (input_reg[6:2] == 5'b00001)
     res = tuple3(True,4'd10,5);
   else if (input_reg[6:1] == 6'b000001)
     res = tuple3(True,4'd11,6);
   else if (input_reg[6:0] == 7'b0000001)
     res = tuple3(True,4'd12,7);
   else
     res = tuple3(False,4'd0,7);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(5)) decode_dct_dc_size_chroma4 (Bit#(4) input_reg);
   Tuple3#(Bool,Bit#(4),Bit#(5)) res;
   if (input_reg[3:2] == 2'b11)
     res = tuple3(True,4'd0,2);
   else if (input_reg[3:2] == 2'b10)
     res = tuple3(True,4'd1,2);
   else if (input_reg[3:2] == 2'b01)
     res = tuple3(True,4'd2,2);
   else if (input_reg[3:1] == 3'b001)
     res = tuple3(True,4'd3,3);
   else if (input_reg[3:0] == 4'b0001)
     res = tuple3(True,4'd4,4);
   else
     res = tuple3(False,4'd0,4);
   return res;
endfunction

function Tuple3#(Bool,Bit#(4),Bit#(5)) decode_dct_dc_size_chroma8 (Bit#(8) input_reg);
   Tuple3#(Bool,Bit#(4),Bit#(5)) res;
   if (input_reg[7] == 1)
     res = tuple3(True,4'd5,1);
   else if (input_reg[7:6] == 2'b01)
     res = tuple3(True,4'd6,2);
   else if (input_reg[7:5] == 3'b001)
     res = tuple3(True,4'd7,3);
   else if (input_reg[7:4] == 4'b0001)
     res = tuple3(True,4'd8,4);
   else if (input_reg[7:3] == 5'b00001)
     res = tuple3(True,4'd9,5);
   else if (input_reg[7:2] == 6'b000001)
     res = tuple3(True,4'd10,6);
   else if (input_reg[7:1] == 7'b0000001)
     res = tuple3(True,4'd11,7);
   else if (input_reg[7:0] == 8'b00000001)
     res = tuple3(True,4'd12,8);
   else
     res = tuple3(False,4'd0,8);
   return res;
endfunction

function Bit#(10) func_get_dc_scaler (Bool cond , Bit#(3) blk_cnt , Bit#(10) qp);
   Bit#(10) res;
     if (cond)
	   res = 10'd8;
	 else
	   begin
	     if (qp < 5)
		   res = 10'd8;
		 else if (qp < 9 && blk_cnt < 4)
		   res = 2*qp;
		 else if (qp < 25 && blk_cnt < 4)
		   res = qp + 8;
		 else if (qp < 25 && blk_cnt >= 4)
		   res = (qp + 13) >> 1;
		 else if (qp >= 25 && blk_cnt >= 4)
		   res = qp -6;
		 else if (qp >= 25 && blk_cnt < 4)
		   res = (qp << 1) - 16;
		 else
		   res = 1;
	   end
   return res;
endfunction

function Bit#(6) inverse_scan_zigzag (Bit#(6) input_reg);
   Bit#(6) res;
     case (input_reg)
	   6'd0  : res = 6'd0;
	   6'd1  : res = 6'd1;
	   6'd2  : res = 6'd8;
	   6'd3  : res = 6'd16;
	   6'd4  : res = 6'd9;
	   6'd5  : res = 6'd2;
	   6'd6  : res = 6'd3;
	   6'd7  : res = 6'd10;
	   6'd8  : res = 6'd17;
	   6'd9  : res = 6'd24;
	   6'd10 : res = 6'd32;
	   6'd11 : res = 6'd25;
	   6'd12 : res = 6'd18;
	   6'd13 : res = 6'd11;
	   6'd14 : res = 6'd4;
	   6'd15 : res = 6'd5;
	   6'd16 : res = 6'd12;
	   6'd17 : res = 6'd19;
	   6'd18 : res = 6'd26;
	   6'd19 : res = 6'd33;
	   6'd20 : res = 6'd40;
	   6'd21 : res = 6'd48;
	   6'd22 : res = 6'd41;
	   6'd23 : res = 6'd34;
	   6'd24 : res = 6'd27;
	   6'd25 : res = 6'd20;
	   6'd26 : res = 6'd13;
	   6'd27 : res = 6'd6;
	   6'd28 : res = 6'd7;
	   6'd29 : res = 6'd14;
	   6'd30 : res = 6'd21;
	   6'd31 : res = 6'd28;
	   6'd32 : res = 6'd35;
	   6'd33 : res = 6'd42;
	   6'd34 : res = 6'd49;
	   6'd35 : res = 6'd56;
	   6'd36 : res = 6'd57;
	   6'd37 : res = 6'd50;
	   6'd38 : res = 6'd43;
	   6'd39 : res = 6'd36;
	   6'd40 : res = 6'd29;
	   6'd41 : res = 6'd22;
	   6'd42 : res = 6'd15;
	   6'd43 : res = 6'd23;
	   6'd44 : res = 6'd30;
	   6'd45 : res = 6'd37;
	   6'd46 : res = 6'd44;
	   6'd47 : res = 6'd51;
	   6'd48 : res = 6'd58;
	   6'd49 : res = 6'd59;
	   6'd50 : res = 6'd52;
	   6'd51 : res = 6'd45;
	   6'd52 : res = 6'd38;
	   6'd53 : res = 6'd31;
	   6'd54 : res = 6'd39;
	   6'd55 : res = 6'd46;
	   6'd56 : res = 6'd53;
	   6'd57 : res = 6'd60;
	   6'd58 : res = 6'd61;
	   6'd59 : res = 6'd54;
	   6'd60 : res = 6'd47;
	   6'd61 : res = 6'd55;
	   6'd62 : res = 6'd62;
	   6'd63 : res = 6'd63;
	   default : res = 0;
     endcase
   return res;
endfunction

function Bit#(6) inverse_scan_alternate_horizontal (Bit#(6) input_reg);
   Bit#(6) res;
     case (input_reg)
	   6'd0  : res = 6'd0;
	   6'd1  : res = 6'd1;
	   6'd2  : res = 6'd2;
	   6'd3  : res = 6'd3;
	   6'd4  : res = 6'd8;
	   6'd5  : res = 6'd9;
	   6'd6  : res = 6'd16;
	   6'd7  : res = 6'd17;
	   6'd8  : res = 6'd10;
	   6'd9  : res = 6'd11;
	   6'd10 : res = 6'd4;
	   6'd11 : res = 6'd5;
	   6'd12 : res = 6'd6;
	   6'd13 : res = 6'd7;
	   6'd14 : res = 6'd15;
	   6'd15 : res = 6'd14;
	   6'd16 : res = 6'd13;
	   6'd17 : res = 6'd12;
	   6'd18 : res = 6'd19;
	   6'd19 : res = 6'd18;
	   6'd20 : res = 6'd24;
	   6'd21 : res = 6'd25;
	   6'd22 : res = 6'd32;
	   6'd23 : res = 6'd33;
	   6'd24 : res = 6'd26;
	   6'd25 : res = 6'd27;
	   6'd26 : res = 6'd20;
	   6'd27 : res = 6'd21;
	   6'd28 : res = 6'd22;
	   6'd29 : res = 6'd23;
	   6'd30 : res = 6'd28;
	   6'd31 : res = 6'd29;
	   6'd32 : res = 6'd30;
	   6'd33 : res = 6'd31;
	   6'd34 : res = 6'd34;
	   6'd35 : res = 6'd35;
	   6'd36 : res = 6'd40;
	   6'd37 : res = 6'd41;
	   6'd38 : res = 6'd48;
	   6'd39 : res = 6'd49;
	   6'd40 : res = 6'd42;
	   6'd41 : res = 6'd43;
	   6'd42 : res = 6'd36;
	   6'd43 : res = 6'd37;
	   6'd44 : res = 6'd38;
	   6'd45 : res = 6'd39;
	   6'd46 : res = 6'd44;
	   6'd47 : res = 6'd45;
	   6'd48 : res = 6'd46;
	   6'd49 : res = 6'd47;
	   6'd50 : res = 6'd50;
	   6'd51 : res = 6'd51;
	   6'd52 : res = 6'd56;
	   6'd53 : res = 6'd57;
	   6'd54 : res = 6'd58;
	   6'd55 : res = 6'd59;
	   6'd56 : res = 6'd52;
	   6'd57 : res = 6'd53;
	   6'd58 : res = 6'd54;
	   6'd59 : res = 6'd55;
	   6'd60 : res = 6'd60;
	   6'd61 : res = 6'd61;
	   6'd62 : res = 6'd62;
	   6'd63 : res = 6'd63;
	   default : res = 0;
     endcase
   return res;
endfunction

function Bit#(6) inverse_scan_alternate_vertical (Bit#(6) input_reg);
   Bit#(6) res;
     case (input_reg)
	   6'd0  : res = 6'd0;
	   6'd8  : res = 6'd1;
	   6'd16  : res = 6'd2;
	   6'd24  : res = 6'd3;
	   6'd32  : res = 6'd8;
	   6'd40  : res = 6'd9;
	   6'd48  : res = 6'd16;
	   6'd56  : res = 6'd17;
	   6'd1  : res = 6'd10;
	   6'd9  : res = 6'd11;
	   6'd17 : res = 6'd4;
	   6'd25 : res = 6'd5;
	   6'd33 : res = 6'd6;
	   6'd41 : res = 6'd7;
	   6'd49 : res = 6'd15;
	   6'd57 : res = 6'd14;
	   6'd2 : res = 6'd13;
	   6'd10 : res = 6'd12;
	   6'd18 : res = 6'd19;
	   6'd26 : res = 6'd18;
	   6'd34 : res = 6'd24;
	   6'd42 : res = 6'd25;
	   6'd50 : res = 6'd32;
	   6'd58 : res = 6'd33;
	   6'd3 : res = 6'd26;
	   6'd11 : res = 6'd27;
	   6'd19 : res = 6'd20;
	   6'd27 : res = 6'd21;
	   6'd35 : res = 6'd22;
	   6'd43 : res = 6'd23;
	   6'd51 : res = 6'd28;
	   6'd59 : res = 6'd29;
	   6'd4 : res = 6'd30;
	   6'd12 : res = 6'd31;
	   6'd20 : res = 6'd34;
	   6'd28 : res = 6'd35;
	   6'd36 : res = 6'd40;
	   6'd44 : res = 6'd41;
	   6'd52 : res = 6'd48;
	   6'd60 : res = 6'd49;
	   6'd5 : res = 6'd42;
	   6'd13 : res = 6'd43;
	   6'd21 : res = 6'd36;
	   6'd29 : res = 6'd37;
	   6'd37 : res = 6'd38;
	   6'd45 : res = 6'd39;
	   6'd53 : res = 6'd44;
	   6'd61 : res = 6'd45;
	   6'd6 : res = 6'd46;
	   6'd14 : res = 6'd47;
	   6'd22 : res = 6'd50;
	   6'd30 : res = 6'd51;
	   6'd38 : res = 6'd56;
	   6'd46 : res = 6'd57;
	   6'd54 : res = 6'd58;
	   6'd62 : res = 6'd59;
	   6'd7 : res = 6'd52;
	   6'd15 : res = 6'd53;
	   6'd23 : res = 6'd54;
	   6'd31 : res = 6'd55;
	   6'd39 : res = 6'd60;
	   6'd47 : res = 6'd61;
	   6'd55 : res = 6'd62;
	   6'd63 : res = 6'd63;
	   default : res = 0;
     endcase
   return res;
endfunction

function Bit#(5) decode_length (Bit#(13) input_reg);
   Bit#(5) res;
   if (input_reg <=2)
     res = 1;
   else if (input_reg <=4)
     res = 2;
   else if (input_reg <=8)
     res = 3;
   else if (input_reg <=16)
     res = 4;
   else if (input_reg <=32)
     res = 5;
   else if (input_reg <=64)
     res = 6;
   else if (input_reg <=128)
     res = 7;
   else if (input_reg <=256)
     res = 8;
   else 
     res = 9;
   return res;
endfunction

/*
(* always_enabled,
   always_ready,
   synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)
module mkDetstartCode(DetstartCode_IFC);

  method detstartcode(byte_align_pos,input_reg,datain);
    detstartcode = func_detstartcode(byte_align_pos,input_reg,datain);
  endmethod: getdata
endmodule: mkByteAlign
*/

endpackage : DetstartCode
