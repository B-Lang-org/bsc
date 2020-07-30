import Real::*;
import FloatingPoint::*;
import StmtFSM::*;
import FShow::*;
import DefaultValue::*;
import Vector::*;

   
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
module sysArith();
   Reg#(FP16) zero  <- mkReg(fromInteger(0));
      
   Vector#(7, FP16) boundaryvals;
   boundaryvals[0] = infinity(True);
   boundaryvals[1] = fromInteger(-1);
   boundaryvals[2] = -fromInteger(0);
   boundaryvals[3] = fromInteger(0);
   boundaryvals[4] = fromInteger(1);
   boundaryvals[5] = infinity(False);
   boundaryvals[6] = snan();

   Stmt test = 
   seq
      delay(10);
      // verify addition
      action
	 FP16 a, b;
	 
	 // verify carry out bit set
	 // 2 + 2 = 4
	 a = fromInteger(2);
	 b = fromInteger(2);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("2 + 2 = ", fshow(a+b));

	 // 2 + -2 = 0
	 a = fromInteger(2);
	 b = fromInteger(-2);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("2 + -2 = ", fshow(a+b));

	 // -2 + 2 = 0
	 a = fromInteger(-2);
	 b = fromInteger(2);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-2 + 2 = ", fshow(a+b));

	 // -2 + -2 = -4
	 a = fromInteger(-2);
	 b = fromInteger(-2);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-2 + -2 = ", fshow(a+b));
	 
	 // 100 + 103
	 a = fromInteger(100);
	 b = fromInteger(103);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("100 + 103 = ", fshow(a+b));

	 // 65504 + 32768 (overflow)
	 a = fromInteger(65504);
	 b = fromInteger(32768);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("65504 + 32768 = ", fshow(a+b));

	 // -65504 + -32768 (overflow)
	 a = fromInteger(-65504);
	 b = fromInteger(-32768);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-65504 + -32768 = ", fshow(a+b));
	 
	 // // verify subnormal addition

	 // 5.960464478e-8 + 5.960464478e-8
	 a = fromReal(5.960464478e-8);
	 b = fromReal(5.960464478e-8);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("5.96e-8 + 5.96e-8 = ", fshow(a+b));
	 	 
	 // -5.960464478e-8 + -5.960464478e-8
	 a = fromReal(-5.960464478e-8);
	 b = fromReal(-5.960464478e-8);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-5.96e-8 + -5.96e-8 = ", fshow(a+b));
	 
	 // 5.960464478e-8 + -5.960464478e-8
	 a = fromReal(5.960464478e-8);
	 b = fromReal(-5.960464478e-8);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("5.96e-8 + -5.96e-8 = ", fshow(a+b));
	 
	 // -5.960464478e-8 + 5.960464478e-8
	 a = fromReal(-5.960464478e-8);
	 b = fromReal(5.960464478e-8);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-5.96e-8 + 5.96e-8 = ", fshow(a+b));
	 
	 // verify case where normalization is necessary
	 
	 // 100 + -103
	 a = fromInteger(100);
	 b = fromInteger(-103);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("100 + -103 = ", fshow(a+b));

	 // -100 + 103
	 a = fromInteger(-100);
	 b = fromInteger(103);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("-100 + 103 = ", fshow(a+b));

	 // 1e-7 + 2e-6
	 a = fromReal(1e-7);
	 b = fromReal(2e-6);
	 FP16 c = fromReal(2.1e-6);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("1e-7 + 2e-6 = ", fshow(a+b));
	 $display("c=", fshow(c));
	 	 
	 // 100 + .25 = 100.25
	 a = fromReal(0.25);
	 b = fromInteger(100);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 $display("100 + .25 = ", fshow(a+b));
	 
	 // 3.25x10^3 + 2.63*10^-1
	 a = fromReal(3.25e3);
	 b = fromReal(2.63e-1);
	 $display("a= ", fshow(a));
	 $display("b= ", fshow(b));
	 $display("3.25*10^3 + 2.63*10^-1 = ", fshow(a+b));
	 
	 // verify subnormal rollover to normal
	 a = unpack('b0_00000_1111111111_11_1);
	 b = unpack('b0_00000_0000000000_00_1);
	 $display("a= ", fshow(a));
	 $display("b= ", fshow(b));
	 $display("a+b= ", fshow(a+b));
	 
	 a = unpack('b0_00000_1111111111_00_0);
	 b = unpack('b0_00000_0000000001_00_0);
	 $display("a= ", fshow(a));
	 $display("b= ", fshow(b));
	 $display("a+b= ", fshow(a+b));
	 
      endaction
      // verify subtraction
      action
      	 FP16 a, b;
	 
      	 // verify carry out bit set
      	 // 2 - 2 = 0
      	 a = fromInteger(2);
      	 b = fromInteger(2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("2 - 2 = ", fshow(a-b));

      	 // 2 - -2 = 4
      	 a = fromInteger(2);
      	 b = fromInteger(-2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("2 - -2 = ", fshow(a-b));

      	 // -2 - 2 = -4
      	 a = fromInteger(-2);
      	 b = fromInteger(2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-2 - 2 = ", fshow(a-b));

      	 // -2 - -2 = 0
      	 a = fromInteger(-2);
      	 b = fromInteger(-2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-2 - -2 = ", fshow(a-b));
	 
      	 // 100 - 103
      	 a = fromInteger(100);
      	 b = fromInteger(103);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("100 - 103 = ", fshow(a-b));

      	 // 65504 - 32768
      	 a = fromInteger(65504);
      	 b = fromInteger(32768);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("65504 - 32768 = ", fshow(a-b));

      	 // -65504 - -32768
      	 a = fromInteger(-65504);
      	 b = fromInteger(-32768);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-65504 - -32768 = ", fshow(a-b));

      	 // -65504 - 32768 (overflow)
      	 a = fromInteger(-65504);
      	 b = fromInteger(32768);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-65504 - 32768 = ", fshow(a-b));

      	 // 65504 - -32768 (overflow)
      	 a = fromInteger(65504);
      	 b = fromInteger(-32768);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("65504 - -32768 = ", fshow(a-b));
	 
      	 // verify subnormal addition

      	 // 5.960464478e-8 - 5.960464478e-8
      	 a = fromReal(5.960464478e-8);
      	 b = fromReal(5.960464478e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("5.96e-8 - 5.96e-8 = ", fshow(a-b));
	 	 
      	 // -5.960464478e-8 - -5.960464478e-8
      	 a = fromReal(-5.960464478e-8);
      	 b = fromReal(-5.960464478e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-5.96e-8 - -5.96e-8 = ", fshow(a-b));
	 
      	 // 5.960464478e-8 - -5.960464478e-8
      	 a = fromReal(5.960464478e-8);
      	 b = fromReal(-5.960464478e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("5.96e-8 - -5.96e-8 = ", fshow(a-b));
	 
      	 // -5.960464478e-8 - 5.960464478e-8
      	 a = fromReal(-5.960464478e-8);
      	 b = fromReal(5.960464478e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-5.96e-8 - 5.96e-8 = ", fshow(a-b));
	 
      	 // verify case where normalization is necessary
	 
      	 // 100 - -103
      	 a = fromInteger(100);
      	 b = fromInteger(-103);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("100 - -103 = ", fshow(a-b));

      	 // -100 - 103
      	 a = fromInteger(-100);
      	 b = fromInteger(103);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-100 - 103 = ", fshow(a-b));

      	 // 1e-7 - 2e-6
      	 a = fromReal(1e-7);
      	 b = fromReal(2e-6);
      	 FP16 c = fromReal(-1.9e-6);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("1e-7 - 2e-6 = ", fshow(a-b));
      	 $display("c=", fshow(c));
	 	 
      	 // 100 - .25 = 99.75
      	 a = fromReal(0.25);
      	 b = fromInteger(100);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("100 - .25 = ", fshow(a-b));
	 
      	 // 3.25x10^3 - 2.63*10^-1
      	 a = fromReal(3.25e3);
      	 b = fromReal(2.63e-1);
      	 $display("a= ", fshow(a));
      	 $display("b= ", fshow(b));
      	 $display("3.25*10^3 - 2.63*10^-1 = ", fshow(a-b));
	 
	 // verify normal rollover to subnormal
	 a = unpack('b0_00001_0000000000_00_0);
	 b = unpack('b0_00000_1000000000_00_0);
	 $display("a= ", fshow(a));
	 $display("b= ", fshow(b));
	 $display("a-b= ", fshow(a-b));
	 
	 a = unpack('b0_00001_0000000000_00_0);
	 b = unpack('b0_00000_0000000001_11_1);
	 $display("a= ", fshow(a));
	 $display("b= ", fshow(b));
	 $display("a-b= ", fshow(a-b));
      endaction
      // verify multiply
      action
      	 FP16 a; FP16 b;
	 
      	 a = fromInteger(2);
      	 b = fromInteger(2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("2 * 2 = ", fshow(a*b));
	 
      	 a = fromInteger(3);
      	 b = fromInteger(3);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("3 * 3 = ", fshow(a*b));

      	 a = fromInteger(3);
      	 b = fromInteger(5);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("3 * 5 = ", fshow(a*b));
	 
      	 a = fromReal(1.75);
      	 b = fromInteger(-5);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("1.75 * -5 = ", fshow(a*b));

      	 a = fromReal(5.960464478e-8);
      	 b = fromReal(5.960464478e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("5.96e-8 * 5.96e-8 = ", fshow(a*b));

      	 a = fromReal(5.960464478e-8);
      	 b = fromReal(2.0);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("5.96e-8 * 2 = ", fshow(a*b));
      	 FP16 c = fromReal(11.920928956e-8);
      	 $display("c=", fshow(c));
	 
      	 a = fromInteger(32768);
      	 b = fromInteger(2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("32768 * 2 = ", fshow(a*b));
      endaction
      // verify divide
      action
      	 FP16 a, b, c;
	 
      	 a = fromReal(4.0);
      	 b = fromReal(2.0);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("4/2 = ", fshow(a/b));

      	 a = fromReal(-4.0);
      	 b = fromReal(2.0);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-4/2 = ", fshow(a/b));

      	 a = fromReal(-4.0);
      	 b = fromReal(-2.0);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("-4/-2 = ", fshow(a/b));

      	 a = fromReal(4.0);
      	 b = fromReal(-2.0);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("4/-2 = ", fshow(a/b));
	 
      	 a = fromInteger(5);
      	 b = fromInteger(4);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("5/4 = ", fshow(a/b));
	 
      	 a = fromInteger(1);
      	 b = fromReal(2.5);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("1/2.5 = ", fshow(a/b));
      	 c = fromReal(0.4);
      	 $display("c=", fshow(c));
	 
      	 a = fromReal(11.920928956e-8);
      	 b = fromInteger(2);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("11.92e-8/2 = ", fshow(a/b));
      	 c = fromReal(5.960464478e-8);
      	 $display("c=", fshow(c));

      	 a = fromReal(11.920928956e-8);
      	 b = fromReal(11.920928956e-8);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("11.92e-8/11.92e-8 = ", fshow(a/b));
      	 c = fromInteger(1);
      	 $display("c=", fshow(c));
	 
      	 a = fromInteger(65504);
      	 b = fromInteger(7);
      	 $display("a=", fshow(a));
      	 $display("b=", fshow(b));
      	 $display("65504/7 = ", fshow(a/b));
      	 c = fromReal(9357.714285714);
      	 $display("c=", fshow(c));
      endaction
      // verify boundary addition
      action
      	 FP16 a, b, c;
	 	 
      	 Vector#(7, Vector#(7, FP16)) adds = newVector;
      	 // -inf
      	 adds[0][0] = infinity(True);
      	 adds[0][1] = infinity(True);
      	 adds[0][2] = infinity(True);
      	 adds[0][3] = infinity(True);
      	 adds[0][4] = infinity(True);
      	 adds[0][5] = snan();
      	 adds[0][6] = snan();
      	 // -1
      	 adds[1][0] = infinity(True);
      	 adds[1][1] = fromInteger(-2);
      	 adds[1][2] = fromInteger(-1);
      	 adds[1][3] = fromInteger(-1);
      	 adds[1][4] = fromInteger(0);
      	 adds[1][5] = infinity(False);
      	 adds[1][6] = snan();
      	 // -0
      	 adds[2][0] = infinity(True);
      	 adds[2][1] = fromInteger(-1);
      	 adds[2][2] = -fromInteger(0);
      	 adds[2][3] = fromInteger(0);
      	 adds[2][4] = fromInteger(1);
      	 adds[2][5] = infinity(False);
      	 adds[2][6] = snan();
      	 // 0
      	 adds[3][0] = infinity(True);
      	 adds[3][1] = fromInteger(-1);
      	 adds[3][2] = fromInteger(0);
      	 adds[3][3] = fromInteger(0);
      	 adds[3][4] = fromInteger(1);
      	 adds[3][5] = infinity(False);
      	 adds[3][6] = snan();
      	 // 1
      	 adds[4][0] = infinity(True);
      	 adds[4][1] = fromInteger(0);
      	 adds[4][2] = fromInteger(1);
      	 adds[4][3] = fromInteger(1);
      	 adds[4][4] = fromInteger(2);
      	 adds[4][5] = infinity(False);
      	 adds[4][6] = snan();
      	 // inf
      	 adds[5][0] = snan();
      	 adds[5][1] = infinity(False);
      	 adds[5][2] = infinity(False);
      	 adds[5][3] = infinity(False);
      	 adds[5][4] = infinity(False);
      	 adds[5][5] = infinity(False);
      	 adds[5][6] = snan();
      	 // nan
      	 adds[6][0] = snan();
      	 adds[6][1] = snan();
      	 adds[6][2] = snan();
      	 adds[6][3] = snan();
      	 adds[6][4] = snan();
      	 adds[6][5] = snan();
      	 adds[6][6] = snan();
	 
      	 $display("Addition");
      	 for(Integer j = 0; j < 7; j = j + 1) begin
      	    for(Integer i = 0; i < 7; i = i + 1) begin
      	       a = boundaryvals[j];
      	       b = boundaryvals[i];
      	       $display("i=%d j=%d", i, j);
      	       $display("a=",fshow(a));
      	       $display("b=",fshow(b));
      	       c = a + b;
      	       $display("ans=",fshow(c));
      	       $display("c  =",fshow(adds[j][i]));
      	       if (c != adds[j][i]) $display("ERROR: MISMATCH!");
      	    end
      	 end
      endaction
      // verify boundary subtraction
      action
      	 FP16 a, b, c;
	 	 
      	 Vector#(7, Vector#(7, FP16)) subs = newVector;
      	 // -inf
      	 subs[0][0] = snan();
      	 subs[0][1] = infinity(True);
      	 subs[0][2] = infinity(True);
      	 subs[0][3] = infinity(True);
      	 subs[0][4] = infinity(True);
      	 subs[0][5] = infinity(True);
      	 subs[0][6] = snan();
      	 // -1
      	 subs[1][0] = infinity(False);
      	 subs[1][1] = fromInteger(0);
      	 subs[1][2] = fromInteger(-1);
      	 subs[1][3] = fromInteger(-1);
      	 subs[1][4] = fromInteger(-2);
      	 subs[1][5] = infinity(True);
      	 subs[1][6] = snan();
      	 // -0
      	 subs[2][0] = infinity(False);
      	 subs[2][1] = fromInteger(1);
      	 subs[2][2] = fromInteger(0);
      	 subs[2][3] = -fromInteger(0);
      	 subs[2][4] = fromInteger(-1);
      	 subs[2][5] = infinity(True);
      	 subs[2][6] = snan();
      	 // 0
      	 subs[3][0] = infinity(False);
      	 subs[3][1] = fromInteger(1);
      	 subs[3][2] = fromInteger(0);
      	 subs[3][3] = fromInteger(0);
      	 subs[3][4] = fromInteger(-1);
      	 subs[3][5] = infinity(True);
      	 subs[3][6] = snan();
      	 // 1
      	 subs[4][0] = infinity(False);
      	 subs[4][1] = fromInteger(2);
      	 subs[4][2] = fromInteger(1);
      	 subs[4][3] = fromInteger(1);
      	 subs[4][4] = fromInteger(0);
      	 subs[4][5] = infinity(True);
      	 subs[4][6] = snan();
      	 // inf
      	 subs[5][0] = infinity(False);
      	 subs[5][1] = infinity(False);
      	 subs[5][2] = infinity(False);
      	 subs[5][3] = infinity(False);
      	 subs[5][4] = infinity(False);
      	 subs[5][5] = snan();
      	 subs[5][6] = snan();
      	 // nan
      	 subs[6][0] = snan();
      	 subs[6][1] = snan();
      	 subs[6][2] = snan();
      	 subs[6][3] = snan();
      	 subs[6][4] = snan();
      	 subs[6][5] = snan();
      	 subs[6][6] = snan();
	 
      	 $display("Subtraction");
      	 for(Integer j = 0; j < 7; j = j + 1) begin
      	    for(Integer i = 0; i < 7; i = i + 1) begin
      	       a = boundaryvals[j];
      	       b = boundaryvals[i];
      	       $display("i=%d j=%d", i, j);
      	       $display("a=",fshow(a));
      	       $display("b=",fshow(b));
      	       c = a - b;
      	       $display("ans=",fshow(c));
      	       $display("c  =",fshow(subs[j][i]));
      	       if (c != subs[j][i]) $display("ERROR: MISMATCH!");
      	    end
      	 end
      endaction
      // verify boundary multiplication
      action
      	 FP16 a, b, c;
	 	 
      	 Vector#(7, Vector#(7, FP16)) subs = newVector;
      	 // -inf
      	 subs[0][0] = infinity(False);
      	 subs[0][1] = infinity(False);
      	 subs[0][2] = snan();
      	 subs[0][3] = snan();
      	 subs[0][4] = infinity(True);
      	 subs[0][5] = infinity(True);
      	 subs[0][6] = snan();
      	 // -1
      	 subs[1][0] = infinity(False);
      	 subs[1][1] = fromInteger(1);
      	 subs[1][2] = fromInteger(0);
      	 subs[1][3] = -fromInteger(-0);
      	 subs[1][4] = fromInteger(-1);
      	 subs[1][5] = infinity(True);
      	 subs[1][6] = snan();
      	 // -0
      	 subs[2][0] = snan();
      	 subs[2][1] = fromInteger(0);
      	 subs[2][2] = fromInteger(0);
      	 subs[2][3] = -fromInteger(0);
      	 subs[2][4] = -fromInteger(0);
      	 subs[2][5] = snan();
      	 subs[2][6] = snan();
      	 // 0
      	 subs[3][0] = snan();
      	 subs[3][1] = -fromInteger(0);
      	 subs[3][2] = -fromInteger(0);
      	 subs[3][3] = fromInteger(0);
      	 subs[3][4] = fromInteger(0);
      	 subs[3][5] = snan();
      	 subs[3][6] = snan();
      	 // 1
      	 subs[4][0] = infinity(True);
      	 subs[4][1] = fromInteger(-1);
      	 subs[4][2] = -fromInteger(0);
      	 subs[4][3] = fromInteger(0);
      	 subs[4][4] = fromInteger(1);
      	 subs[4][5] = infinity(False);
      	 subs[4][6] = snan();
      	 // inf
      	 subs[5][0] = infinity(True);
      	 subs[5][1] = infinity(True);
      	 subs[5][2] = snan();
      	 subs[5][3] = snan();
      	 subs[5][4] = infinity(False);
      	 subs[5][5] = infinity(False);
      	 subs[5][6] = snan();
      	 // nan
      	 subs[6][0] = snan();
      	 subs[6][1] = snan();
      	 subs[6][2] = snan();
      	 subs[6][3] = snan();
      	 subs[6][4] = snan();
      	 subs[6][5] = snan();
      	 subs[6][6] = snan();
	 
      	 $display("Multiplication");
      	 for(Integer j = 0; j < 7; j = j + 1) begin
      	    for(Integer i = 0; i < 7; i = i + 1) begin
      	       a = boundaryvals[j];
      	       b = boundaryvals[i];
      	       $display("i=%d j=%d", i, j);
      	       $display("a=",fshow(a));
      	       $display("b=",fshow(b));
      	       c = a * b;
      	       $display("ans=",fshow(c));
      	       $display("c  =",fshow(subs[j][i]));
      	       if (c != subs[j][i]) $display("ERROR: MISMATCH!");
      	    end
      	 end
      endaction
      // verify boundary division
      action
      	 FP16 a, b, c;
	 	 
      	 Vector#(7, Vector#(7, FP16)) subs = newVector;
      	 // -inf
      	 subs[0][0] = snan();
      	 subs[0][1] = infinity(False);
      	 subs[0][2] = infinity(False);
      	 subs[0][3] = infinity(True);
      	 subs[0][4] = infinity(True);
      	 subs[0][5] = snan();
      	 subs[0][6] = snan();
      	 // -1
      	 subs[1][0] = fromInteger(0);
      	 subs[1][1] = fromInteger(1);
      	 subs[1][2] = infinity(False);
      	 subs[1][3] = infinity(True);
      	 subs[1][4] = fromInteger(-1);
      	 subs[1][5] = -fromInteger(0);
      	 subs[1][6] = snan();
      	 // -0
      	 subs[2][0] = fromInteger(0);
      	 subs[2][1] = fromInteger(0);
      	 subs[2][2] = snan();
      	 subs[2][3] = snan();
      	 subs[2][4] = -fromInteger(0);
      	 subs[2][5] = -fromInteger(0);
      	 subs[2][6] = snan();
      	 // 0
      	 subs[3][0] = -fromInteger(0);
      	 subs[3][1] = -fromInteger(0);
      	 subs[3][2] = snan();
      	 subs[3][3] = snan();
      	 subs[3][4] = fromInteger(0);
      	 subs[3][5] = fromInteger(0);
      	 subs[3][6] = snan();
      	 // 1
      	 subs[4][0] = -fromInteger(0);
      	 subs[4][1] = fromInteger(-1);
      	 subs[4][2] = infinity(True);
      	 subs[4][3] = infinity(False);
      	 subs[4][4] = fromInteger(1);
      	 subs[4][5] = fromInteger(0);
      	 subs[4][6] = snan();
      	 // inf
      	 subs[5][0] = snan();
      	 subs[5][1] = infinity(True);
      	 subs[5][2] = infinity(True);
      	 subs[5][3] = infinity(False);
      	 subs[5][4] = infinity(False);
      	 subs[5][5] = snan();
      	 subs[5][6] = snan();
      	 // nan
      	 subs[6][0] = snan();
      	 subs[6][1] = snan();
      	 subs[6][2] = snan();
      	 subs[6][3] = snan();
      	 subs[6][4] = snan();
      	 subs[6][5] = snan();
      	 subs[6][6] = snan();
	 
      	 $display("Division");
      	 for(Integer j = 0; j < 7; j = j + 1) begin
      	    for(Integer i = 0; i < 7; i = i + 1) begin
      	       a = boundaryvals[j];
      	       b = boundaryvals[i];
      	       $display("i=%d j=%d", i, j);
      	       $display("a=",fshow(a));
      	       $display("b=",fshow(b));
      	       c = a / b;
      	       $display("ans=",fshow(c));
      	       $display("c  =",fshow(subs[j][i]));
      	       if (c != subs[j][i]) $display("ERROR: MISMATCH!");
      	    end
      	 end
      endaction

      action
	 FP64 a, b, c;
	 Double da, db, dc;
	 da = unpack(64'hBBE0_0000_0000_0000);
	 db = da;
	 $display("da=%0X", da);
	 $display("db=%0X", db);
	 a = toFP(da);
	 b = toFP(db);
	 $display("a=", fshow(a));
	 $display("b=", fshow(b));
	 c = a + b;
	 $display("a+b=", fshow(c));
	 dc = fromFP(c);
	 $display("dc=%08X", pack(dc));
      endaction
      
      delay(10);
   endseq;
   
   mkAutoFSM(test);
   
endmodule

