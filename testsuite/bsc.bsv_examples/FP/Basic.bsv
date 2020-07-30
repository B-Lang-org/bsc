import Real::*;
import FloatingPoint::*;
import StmtFSM::*;
import FShow::*;
import DefaultValue::*;

   
   // 0
   // -0
   // epsilon (normalized)
   // -epsilon (normalized)
   // epsilon (denormalized)
   // -epsilon (denormalized)
   // 2
   // 3
   // 2.3
   // -2.3
   // infinity
   // -infinity
   // qnan
   // snan
   // large number
   // -large number
   // max normalized
   // min normalized
   // max denormalized
   // min denormalized

(* synthesize *)
module sysBasic();
   Reg#(FP16) rFP16 <- mkRegU;
   Reg#(Bit#(16)) rBit16 <- mkRegU;
   Reg#(Float16) rFloat16 <- mkRegU;
   Reg#(Int#(16)) rInt16 <- mkRegU;
   
   Reg#(FP32) rFP32 <- mkRegU;
   Reg#(Bit#(32)) rBit32 <- mkRegU;
   Reg#(Float32) rFloat32 <- mkRegU;
   Reg#(Int#(32)) rInt32 <- mkRegU;

   Reg#(FP64) rFP64 <- mkRegU;
   Reg#(Bit#(64)) rBit64 <- mkRegU;
   Reg#(Float64) rFloat64 <- mkRegU;
   Reg#(Int#(64)) rInt64 <- mkRegU;

   Stmt test = 
   seq
      delay(10);
      // verify zextendlsb
      action
	 Bit#(4) x = '1;
	 Bit#(6) y = zExtendLSB(x);
	 $display("zextend: %b %b", x, y);
      endaction
      // verify cextendlsb
      action
	 Bit#(4) x = '1;
	 FP16 y = cExtendLSB(x);
	 $display("cextend: %b %b", x, y);
      endaction
      // verify findIndexOneMSB_
      action
	 Bit#(20) x = '1;
	 x = x >> 4;
	 let xms1 = findIndexOneMSB_(x); // should return 16
	 Bit#(1) y = 1;
	 let yms1 = findIndexOneMSB_(y); // should return 1
	 Bit#(20) z = 0;
	 let zms1 = findIndexOneMSB_(z); // should return 0
	 Bit#(15) w = '1;
	 let wms1 = findIndexOneMSB_(w); // should return 15
	 $display("%d %d %d %d", xms1, yms1, zms1, wms1);
      endaction
      // verify findIndexOneLSB_
      action
	 Bit#(20) x = '1;
	 let xms1 = findIndexOneLSB_(x); // should return 0
	 Bit#(1) y = 0;
	 let yms1 = findIndexOneLSB_(y); // should return 1
	 Bit#(20) z = 1 << 19;
	 let zms1 = findIndexOneLSB_(z); // should return 19
	 Bit#(15) w = 'h7700;
	 let wms1 = findIndexOneLSB_(w); // should return 8
	 $display("%d %d %d %d", xms1, yms1, zms1, wms1);
      endaction
      // verify findIndexOneMSB
      action
	 Bit#(20) x = '1;
	 x = x >> 4;
	 let xms1 = findIndexOneMSB(x); // should return 16
	 Bit#(2) y = 1;
	 let yms1 = findIndexOneMSB(y); // should return 1
	 Bit#(20) z = 0;
	 let zms1 = findIndexOneMSB(z); // should return 0
	 Bit#(15) w = '1;
	 let wms1 = findIndexOneMSB(w); // should return 15
	 $display("%d %d %d %d", xms1, yms1, zms1, wms1);
      endaction
      // verify findIndexOneLSB
      action
	 Bit#(20) x = '1;
	 let xms1 = findIndexOneLSB(x); // should return 0
	 Bit#(2) y = 0;
	 let yms1 = findIndexOneLSB(y); // should return 0
	 Bit#(20) z = 1 << 19;
	 let zms1 = findIndexOneLSB(z); // should return 19
	 Bit#(15) w = 'h7700;
	 let wms1 = findIndexOneLSB(w); // should return 8
	 $display("%d %d %d %d", xms1, yms1, zms1, wms1);
      endaction
      // verify rightshift
      action
       	 FP16 x = defaultValue; x.sfd = '1; x.exp = 0;
       	 $display("rightshift start: %b %b%b", x.sfd, x.round, x.sticky);
       	 x = rightshift(x, 1);
      	 $display("rightshift 1:     %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 2:     %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 3:     %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = '1;
      	 x = rightshift(x, 2);
      	 $display("rightshift 2:     %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = '1;
      	 x = rightshift(x, 3);
      	 $display("rightshift 3:     %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = '1;
      	 x = rightshift(x, 10);
      	 $display("rightshift 10:    %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 11:    %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 12:    %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 13:    %b %b%b", x.sfd, x.round, x.sticky);
      	 x = rightshift(x, 1);
      	 $display("rightshift 14:    %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = '1;
      	 x = rightshift(x, 15);
      	 $display("rightshift 15:    %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = '1;
      	 x = rightshift(x, 31);
      	 $display("rightshift 31:    %b %b%b", x.sfd, x.round, x.sticky);

      	 x = defaultValue; x.sfd = 0;
      	 x = rightshift(x, 31);
      	 $display("rightshift 31:    %b %b%b", x.sfd, x.round, x.sticky);
      endaction
      // verify round zero mode
      action
      	 FloatingPoint#(5,10) a = defaultValue;
	 FloatingPoint#(5,10) b;
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a.sfd = 'b1100000110; a.round = 3; a.sticky = 0;
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1100000111; a.round = 1; a.sticky = 1;
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round(Rnd_Zero, a);
	 $write("", fshow(Rnd_Zero));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify round plus infinity
      action
      	 FloatingPoint#(5,10) a = defaultValue;
      	 FloatingPoint#(5,10) b;
	 
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a.sfd = 'b1100000100; a.round = 2; a.sticky = 0;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1100000100; a.round = 2; a.sticky = 0; a.sign = True;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1100000001; a.round = 1; a.sticky = 0; a.sign = False;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1100000001; a.round = 0; a.sticky = 1;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True;  a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round(Rnd_Plus_Inf, a);
      	 $write("", fshow(Rnd_Plus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify round negative infinity
      action
      	 FloatingPoint#(5,10) a = defaultValue;
      	 FloatingPoint#(5,10) b;
	 
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a.sfd = 'b1100000100; a.round = 2; a.sticky = 0;
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1100000100; a.round = 2; a.sticky = 0; a.sign = True;
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = False; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True;  a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round(Rnd_Minus_Inf, a);
      	 $write("", fshow(Rnd_Minus_Inf));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify round nearest even
      action
      	 FloatingPoint#(5,10) a = defaultValue;
      	 FloatingPoint#(5,10) b;
	 
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 0;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 1; a.sticky = 0;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 1;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 0; a.sticky = 1;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 2; a.sticky = 0;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000001; a.round = 2; a.sticky = 0;
      	 b = round(Rnd_Nearest_Even, a);
	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = False; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Nearest_Even, a);
      	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True;  a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Nearest_Even, a);
      	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round(Rnd_Nearest_Even, a);
      	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round(Rnd_Nearest_Even, a);
      	 $write("", fshow(Rnd_Nearest_Even));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify round nearest away from zero
      action
      	 FloatingPoint#(5,10) a = defaultValue;
      	 FloatingPoint#(5,10) b;
	 
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 0;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 1; a.sticky = 0;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 1;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 0; a.sticky = 1;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 2; a.sticky = 0;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 2; a.sticky = 0; a.sign = True;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = False; a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True;  a.exp = fromInteger(maxexp(a));
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round(Rnd_Nearest_Away_Zero, a);
      	 $write("", fshow(Rnd_Nearest_Away_Zero));
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify default round mode
      action
      	 FloatingPoint#(5,10) a = defaultValue;
      	 FloatingPoint#(5,10) b;
	 
      	 a.sfd = 'b1100000100; a.round = 0; a.sticky = 0;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
	 
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 0;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 1; a.sticky = 0;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 3; a.sticky = 1;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 0; a.sticky = 1;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 2; a.sticky = 0;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      
      	 a = defaultValue;
      	 a.sfd = 'b1100000000; a.round = 2; a.sticky = 0; a.sign = True;
      	 b = round_default(a);
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = False; a.exp = fromInteger(maxexp(a));
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b1111111111; a.round = 3; a.sticky = 1; a.sign = True;  a.exp = fromInteger(maxexp(a));
      	 b = round_default(a);
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = False;
      	 b = round_default(a);
      	 $display("  %b %b %b = %b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);

      	 a.sfd = 'b0000000000; a.round = 3; a.sticky = 1; a.sign = True;
      	 b = round_default(a);
      	 $display("  -%b %b %b = -%b %b %b  ", a.sfd, a.round, a.sticky, b.sfd, b.round, b.sticky);
      endaction
      // verify fromReal (16)
      action
      	 FP16 a;
      	 a = fromReal(0.0);
      	 $display("+0.0 = ", fshow(a));
      	 a = fromReal(-0.0);
      	 $display("-0.0 = ", fshow(a));

      	 a = fromReal(2.0);
      	 $display("+2.0 = ", fshow(a));
      	 a = fromReal(-2.0);
      	 $display("-2.0 = ", fshow(a));

      	 a = fromReal(3.0);
      	 $display("+3.0 = ", fshow(a));
      	 a = fromReal(-3.0);
      	 $display("-3.0 = ", fshow(a));

      	 a = fromReal(2.3);
      	 $display("+2.3 = ", fshow(a));
      	 a = fromReal(-2.3);
      	 $display("-2.3 = ", fshow(a));

      	 a = fromReal(65504);
      	 $display("max normal = ", fshow(a));
      	 a = fromReal(-65504);
      	 $display("min normal = ", fshow(a));
	 
      	 a = fromReal(6.10352e-5);
      	 $display("min pos normal = ", fshow(a));
      	 a = fromReal(-6.10352e-5);
      	 $display("max neg normal = ", fshow(a));
	 
	 a = fromReal(5.960464478e-8);
	 $display("min pos denormal = ", fshow(a));
	 a = fromReal(-5.960464478e-8);
	 $display("max neg denormal = ", fshow(a));

	 a = fromReal(5.960464478e-8*2);
	 $display("min pos denormal<<1 = ", fshow(a));
	 a = fromReal(-5.960464478e-8*2);
	 $display("max neg denormal<<1 = ", fshow(a));
      endaction
      // verify fromReal (32)
      action
      	 FP32 a;
      	 a = fromReal(0.0);
      	 $display("+0.0 = ", fshow(a));
      	 a = fromReal(-0.0);
      	 $display("-0.0 = ", fshow(a));

      	 a = fromReal(2.0);
      	 $display("+2.0 = ", fshow(a));
      	 a = fromReal(-2.0);
      	 $display("-2.0 = ", fshow(a));

      	 a = fromReal(3.0);
      	 $display("+3.0 = ", fshow(a));
      	 a = fromReal(-3.0);
      	 $display("-3.0 = ", fshow(a));

      	 a = fromReal(2.3);
      	 $display("+2.3 = ", fshow(a));
      	 a = fromReal(-2.3);
      	 $display("-2.3 = ", fshow(a));

      	 a = fromReal(3.4028234663852886E+38);
      	 $display("max normal = ", fshow(a));
      	 a = fromReal(-3.4028234663852886E+38);
      	 $display("min normal = ", fshow(a));
	 
      	 a = fromReal(1.1754943508222875E-38);
      	 $display("min pos normal = ", fshow(a));
      	 a = fromReal(-1.1754943508222875E-38);
      	 $display("max neg normal = ", fshow(a));

	 a = fromReal(1.40129846432481707092372958329E-45);
	 $display("min pos denormal = ", fshow(a));
	 a = fromReal(-1.40129846432481707092372958329E-45);
	 $display("max neg denormal = ", fshow(a));

	 a = fromReal(1.40129846432481707092372958329E-45*2);
	 $display("min pos denormal<<1 = ", fshow(a));
	 a = fromReal(-1.40129846432481707092372958329E-45*2);
	 $display("max neg denormal<<1 = ", fshow(a));
      endaction
      // verify fromReal (64)
      action
      	 FP64 a;
      	 a = fromReal(0.0);
      	 $display("+0.0 = ", fshow(a));
      	 a = fromReal(-0.0);
      	 $display("-0.0 = ", fshow(a));

      	 a = fromReal(2.0);
      	 $display("+2.0 = ", fshow(a));
      	 a = fromReal(-2.0);
      	 $display("-2.0 = ", fshow(a));

      	 a = fromReal(3.0);
      	 $display("+3.0 = ", fshow(a));
      	 a = fromReal(-3.0);
      	 $display("-3.0 = ", fshow(a));

      	 a = fromReal(2.3);
      	 $display("+2.3 = ", fshow(a));
      	 a = fromReal(-2.3);
      	 $display("-2.3 = ", fshow(a));

      	 a = fromReal(1.7976931348623157E+308);
      	 $display("max normal = ", fshow(a));
      	 a = fromReal(-1.7976931348623157E+308);
      	 $display("min normal = ", fshow(a));
	 
      	 a = fromReal(2.2250738585072014E-308);
      	 $display("min pos normal = ", fshow(a));
      	 a = fromReal(-2.2250738585072014E-308);
      	 $display("max neg normal = ", fshow(a));

	 a = fromReal(4.94065645841246544176568792868E-324);
	 $display("min pos denormal = ", fshow(a));
	 a = fromReal(-4.94065645841246544176568792868E-324);
	 $display("max neg denormal = ", fshow(a));

	 a = fromReal(4.94065645841246544176568792868E-324*2);
	 $display("min pos denormal<<1 = ", fshow(a));
	 a = fromReal(-4.94065645841246544176568792868E-324*2);
	 $display("max neg denormal<<1 = ", fshow(a));
      endaction
      // verify fromInteger(16)
      action
      	 FP16 a;
      	 a = fromInteger(0);
      	 $display("+0 = ", fshow(a));
	 
      	 a = fromInteger(1);
      	 $display("+1 = ", fshow(a));
      	 a = fromInteger(-1);
      	 $display("-1 = ", fshow(a));
	 
      	 a = fromInteger(2);
      	 $display("+2 = ", fshow(a));
      	 a = fromInteger(-2);
      	 $display("-2 = ", fshow(a));
	 
      	 a = fromInteger(65504);
      	 $display("+maxint = ", fshow(a));
      	 a = fromInteger(-65504);
      	 $display("-maxint = ", fshow(a));
	 
      	 a = fromInteger(32768);
      	 $display("+32768 = ", fshow(a));
      	 a = fromInteger(-32768);
      	 $display("-32768 = ", fshow(a));
      endaction
      // verify fromInteger(32)
      action
      	 FP32 a;
      	 a = fromInteger(0);
      	 $display("+0 = ", fshow(a));
	 
      	 a = fromInteger(1);
      	 $display("+1 = ", fshow(a));
      	 a = fromInteger(-1);
      	 $display("-1 = ", fshow(a));
	 
      	 a = fromInteger(2);
      	 $display("+2 = ", fshow(a));
      	 a = fromInteger(-2);
      	 $display("-2 = ", fshow(a));
	 
      	 a = fromInteger(65503);
      	 $display("+65503 = ", fshow(a));
      	 a = fromInteger(-65503);
      	 $display("-65503 = ", fshow(a));

      	 a = fromInteger(2147483648);
      	 $display("+2147483648 = ", fshow(a));
      	 a = fromInteger(-2147483648);
      	 $display("-2147483648 = ", fshow(a));
      endaction
      // verify fromInteger(64)
      action
      	 FP64 a;
      	 a = fromInteger(0);
      	 $display("+0 = ", fshow(a));
	 
      	 a = fromInteger(1);
      	 $display("+1 = ", fshow(a));
      	 a = fromInteger(-1);
      	 $display("-1 = ", fshow(a));
	 
      	 a = fromInteger(2);
      	 $display("+2 = ", fshow(a));
      	 a = fromInteger(-2);
      	 $display("-2 = ", fshow(a));
	 
      	 a = fromInteger(65505);
      	 $display("+65505 = ", fshow(a));
      	 a = fromInteger(-65505);
      	 $display("-65505 = ", fshow(a));
	 
      	 a = fromInteger(4294967296);
      	 $display("+4294967296 = ", fshow(a));
      	 a = fromInteger(-4294967296);
      	 $display("-4294967296 = ", fshow(a));
      endaction
      // verify ord
      action
      	 FP16 a = fromReal(2.3);
      	 FP16 b = fromReal(-2.3);
      	 FP16 c = fromReal(4.3);
      	 FP16 d = fromReal(2.2);
	 
      	 // less than
      	 $display("-2.3 <  2.3 = %d", (b < a));
      	 $display(" 2.3 < -2.3 = %d", (a < b));
      	 $display(" 2.3 <  4.3 = %d", (a < c));
      	 $display(" 4.3 <  2.3 = %d", (c < a));
      	 $display(" 2.2 <  2.3 = %d", (d < a));
      	 $display(" 2.3 <  2.2 = %d", (a < d));
      	 $display(" 2.3 <  2.3 = %d", (a < a));
	 
      	 // less than equal 
      	 $display("-2.3 <=  2.3 = %d", (b <= a));
      	 $display(" 2.3 <= -2.3 = %d", (a <= b));
      	 $display(" 2.3 <=  4.3 = %d", (a <= c));
      	 $display(" 4.3 <=  2.3 = %d", (c <= a));
      	 $display(" 2.2 <=  2.3 = %d", (d <= a));
      	 $display(" 2.3 <=  2.2 = %d", (a <= d));
      	 $display(" 2.3 <=  2.3 = %d", (a <= a));

      	 // greater than
      	 $display("-2.3 >  2.3 = %d", (b > a));
      	 $display(" 2.3 > -2.3 = %d", (a > b));
      	 $display(" 2.3 >  4.3 = %d", (a > c));
      	 $display(" 4.3 >  2.3 = %d", (c > a));
      	 $display(" 2.2 >  2.3 = %d", (d > a));
      	 $display(" 2.3 >  2.2 = %d", (a > d));
      	 $display(" 2.3 >  2.3 = %d", (a > a));
	 
      	 // greater than equal 
      	 $display("-2.3 >=  2.3 = %d", (b >= a));
      	 $display(" 2.3 >= -2.3 = %d", (a >= b));
      	 $display(" 2.3 >=  4.3 = %d", (a >= c));
      	 $display(" 4.3 >=  2.3 = %d", (c >= a));
      	 $display(" 2.2 >=  2.3 = %d", (d >= a));
      	 $display(" 2.3 >=  2.2 = %d", (a >= d));
      	 $display(" 2.3 >=  2.3 = %d", (a >= a));
	 
	 // subnormals
	 a = fromReal(5.960464478e-8);
	 b = fromReal(11.960464478e-8);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("a < b = %d", (a < b));
	 
	 // compare function
	 a = fromReal(2.3);
	 b = fromReal(2.33);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("compare(a,b) = %d", compare(a,b));

	 a = fromReal(2.3);
	 b = fromReal(2.33);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("compare(b,a) = %d", compare(b,a));

	 a = fromReal(2.33);
	 b = fromReal(2.33);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("compare(b,a) = %d", compare(b,a));
	 
	 // min
	 a = fromReal(2.3);
	 b = fromReal(2.33);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("min(a,b) = ", fshow(min(a,b)));
	 $display("min(b,a) = ", fshow(min(b,a)));

	 // max
	 a = fromReal(2.3);
	 b = fromReal(2.33);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("max(a,b) = ", fshow(max(a,b)));
	 $display("max(b,a) = ", fshow(max(b,a)));
	 
	 // subnormals
	 a = unpack('b0_00000_1111111111_11_1);
	 b = unpack('b0_00001_0000000000_00_0);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("a < b = %d", (a < b));
	 $display("a <= b = %d", (a <= b));
	 $display("a > b = %d", (a > b));
	 $display("a >= b = %d", (a >= b));
	 $display("compare(a,b) = %d", compare(a,b));
	 $display("compare(b,a) = %d", compare(b,a));
	 $display("min(a,b) = ", fshow(min(a,b)));
	 $display("min(b,a) = ", fshow(min(b,a)));
	 $display("max(a,b) = ", fshow(max(a,b)));
	 $display("max(b,a) = ", fshow(max(b,a)));

	 // verify not using rounding bits in compare
	 a = unpack('b0_00000_1111111111_11_1);
	 b = unpack('b0_00000_1111111111_10_0);
	 $display("a = ", fshow(a));
	 $display("b = ", fshow(b));
	 $display("a < b = %d", (a < b));
	 $display("a <= b = %d", (a <= b));
	 $display("a > b = %d", (a > b));
	 $display("a >= b = %d", (a >= b));
	 $display("compare(a,b) = %d", compare(a,b));
	 $display("compare(b,a) = %d", compare(b,a));
	 $display("min(a,b) = ", fshow(min(a,b)));
	 $display("min(b,a) = ", fshow(min(b,a)));
	 $display("max(a,b) = ", fshow(max(a,b)));
	 $display("max(b,a) = ", fshow(max(b,a)));
	 
      endaction
      // verify toInt32
      action 
	 FP64 a = fromReal(0.9);
	 FP64 b = fromReal(1.0);
	 FP64 c = fromReal(33.99);
	 FP64 d = fromReal(-5.9);
	 FP64 e = fromReal(-0.9);
	 
	 $display("0.9   = %d (%x)", toInt32(a), pack(toInt32(a)));
	 $display("1.0   = %d (%x)", toInt32(b), pack(toInt32(b)));
	 $display("33.99 = %d (%x)", toInt32(c), pack(toInt32(c)));
	 $display("-5.9  = %d (%x)", toInt32(d), pack(toInt32(d)));
	 $display("-0.9  = %d (%x)", toInt32(e), pack(toInt32(e)));
      endaction
      action
	 FP32 a = fromReal(0.9);
	 FP32 b = fromReal(1.0);
	 FP32 c = fromReal(33.99);
	 FP32 d = fromReal(-5.9);
	 FP32 e = fromReal(-0.9);
	 
	 $display("0.9   = %d (%x)", toInt32(a), pack(toInt32(a)));
	 $display("1.0   = %d (%x)", toInt32(b), pack(toInt32(b)));
	 $display("33.99 = %d (%x)", toInt32(c), pack(toInt32(c)));
	 $display("-5.9  = %d (%x)", toInt32(d), pack(toInt32(d)));
	 $display("-0.9  = %d (%x)", toInt32(e), pack(toInt32(e)));
      endaction
      action
	 FP16 a = fromReal(0.9);
	 FP16 b = fromReal(1.0);
	 FP16 c = fromReal(33.99);
	 FP16 d = fromReal(-5.9);
	 FP16 e = fromReal(-0.9);
	 
	 $display("0.9   = %d (%x)", toInt32(a), pack(toInt32(a)));
	 $display("1.0   = %d (%x)", toInt32(b), pack(toInt32(b)));
	 $display("33.99 = %d (%x)", toInt32(c), pack(toInt32(c)));
	 $display("-5.9  = %d (%x)", toInt32(d), pack(toInt32(d)));
	 $display("-0.9  = %d (%x)", toInt32(e), pack(toInt32(e)));
      endaction
      // verify fromInt32
      action
	 Int#(32) a = 0;
	 Int#(32) b = 1;
	 Int#(32) c = -1;
	 Int#(32) d = 2;
	 Int#(32) e = 33;
	 Int#(32) f = unpack('h7FFFFFFF);
	 Int#(32) g = unpack('h80000001);
	 
	 FP16 a16 = fromInt32(a);
	 FP16 b16 = fromInt32(b);
	 FP16 c16 = fromInt32(c);
	 FP16 d16 = fromInt32(d);
	 FP16 e16 = fromInt32(e);
	 FP16 f16 = fromInt32(f);
	 FP16 g16 = fromInt32(g);
	 
	 $display("0   = ", fshow(a16));
	 $display("1   = ", fshow(b16));
	 $display("-1  = ", fshow(c16));
	 $display("2   = ", fshow(d16));
	 $display("33  = ", fshow(e16));
	 $display("max = ", fshow(f16));
	 $display("min = ", fshow(g16));
      endaction
      // verify fromInt32
      action
	 Int#(32) a = 0;
	 Int#(32) b = 1;
	 Int#(32) c = -1;
	 Int#(32) d = 2;
	 Int#(32) e = 33;
	 Int#(32) f = unpack('h7FFFFFFF);
	 Int#(32) g = unpack('h80000001);
	 
	 FP32 a16 = fromInt32(a);
	 FP32 b16 = fromInt32(b);
	 FP32 c16 = fromInt32(c);
	 FP32 d16 = fromInt32(d);
	 FP32 e16 = fromInt32(e);
	 FP32 f16 = fromInt32(f);
	 FP32 g16 = fromInt32(g);
	 
	 $display("0   = ", fshow(a16));
	 $display("1   = ", fshow(b16));
	 $display("-1  = ", fshow(c16));
	 $display("2   = ", fshow(d16));
	 $display("33  = ", fshow(e16));
	 $display("max = ", fshow(f16));
	 $display("min = ", fshow(g16));
      endaction
      // verify fromInt32
      action
	 Int#(32) a = 0;
	 Int#(32) b = 1;
	 Int#(32) c = -1;
	 Int#(32) d = 2;
	 Int#(32) e = 33;
	 Int#(32) f = unpack('h7FFFFFFF);
	 Int#(32) g = unpack('h80000001);
	 
	 FP64 a16 = fromInt32(a);
	 FP64 b16 = fromInt32(b);
	 FP64 c16 = fromInt32(c);
	 FP64 d16 = fromInt32(d);
	 FP64 e16 = fromInt32(e);
	 FP64 f16 = fromInt32(f);
	 FP64 g16 = fromInt32(g);
	 
	 $display("0   = ", fshow(a16));
	 $display("1   = ", fshow(b16));
	 $display("-1  = ", fshow(c16));
	 $display("2   = ", fshow(d16));
	 $display("33  = ", fshow(e16));
	 $display("max = ", fshow(f16));
	 $display("min = ", fshow(g16));
      endaction
      // verify fract function
      action
	 FP32 a = snan();
	 FP32 b = snan();
	 
	 // snan
	 a = snan();
	 $display("snan = ", fshow(fract(a)));
	 
	 // +infinity
	 a = infinity(False);
	 $display("+infinity = ", fshow(fract(a)));
	 
	 // -infinity
	 a = infinity(True);
	 $display("-infinity = ", fshow(fract(a)));
	 
	 // subnormal
	 a = fromReal(1.40129846432481707092372958329E-45);
	 $display("1.40e-45 = ", fshow(fract(a)));
	 
	 // between [0-1]
	 a = fromReal(0.4);
	 $display("0.4 = ", fshow(fract(a)));
	 
	 // between [0-1]
	 a = fromReal(0.999);
	 $display("0.999 = ", fshow(fract(a)));
	 
	 // between [1-2)
	 a = fromReal(1.999);
	 $display("1.999 = ", fshow(fract(a)));
	 
	 // other cases
	 a = fromReal(123.456);
	 $display("123.456 = ", fshow(fract(a)));
	 
	 a = fromReal(100.001);
	 $display("100.001 = ", fshow(fract(a)));
	 
	 a = fromReal(99999.999);
	 $display("99999.999 = ", fshow(fract(a)));
	 
	 a = fromReal(0.0002);
	 $display("0.0002 = ", fshow(fract(a)));
	 
	 a = fromReal(-1.999);
	 $display("-1.999 = ", fshow(fract(a)));
	 
	 a = fromReal(0.000);
	 $display("0.000 = ", fshow(fract(a)));
	 
	 a = fromReal(1.000);
	 $display("1.000 = ", fshow(fract(a)));
	 
	 a = fromReal(2.000);
	 $display("2.000 = ", fshow(fract(a)));
	 
	 a = fromReal(1.000);
	 b = fromReal(2.000);
	 $display("2.000-1.000 = ", fshow(fract(b-a)));
	 
	 a = fromInt32(45);
	 b = fromInt32(-15);
	 $display("45-15 = ", fshow(fract(a+b)));
	 
      endaction
      delay(10);
   endseq;
   
   mkAutoFSM(test);
   
endmodule

