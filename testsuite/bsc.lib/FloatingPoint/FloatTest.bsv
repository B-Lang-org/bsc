package FloatTest;

import ClientServer ::*;
import Counter ::*;
import DefaultValue ::*;
import FIFO ::*;
import FIFOF ::*;
import FShow ::*;
import FloatingPoint ::*;
import GetPut ::*;
import Real ::*;
import StmtFSM ::*;
import Divide ::*;
import SquareRoot ::*;

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkFloatingPointDividerDouble(Server#(Tuple3#(Double,Double,RoundMode),Tuple2#(Double,Exception)));
   Server#(Tuple2#(UInt#(114),UInt#(57)),Tuple2#(UInt#(57),UInt#(57))) _div <- mkDivider(1);
   let _ifc <- mkFloatingPointDivider(_div);
   return _ifc;
endmodule

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkFloatingPointSquareRooterDouble(Server#(Tuple2#(Double,RoundMode),Tuple2#(Double,Exception)));
   Server#(UInt#(116),Tuple2#(UInt#(116),Bool)) _sqrt <- mkSquareRooter(1);
   let _ifc <- mkFloatingPointSquareRooter(_sqrt);
   return _ifc;
endmodule

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkFloatingPointFusedMultiplyAccumulateDouble(Server#(Tuple4#(Maybe#(Double),Double,Double,RoundMode),Tuple2#(Double,Exception)));
   let _ifc <- mkFloatingPointFusedMultiplyAccumulate;
   return _ifc;
endmodule

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkFloatingPointAdderDouble(Server#(Tuple3#(Double,Double,RoundMode),Tuple2#(Double,Exception)));
   let _ifc <- mkFloatingPointAdder;
   return _ifc;
endmodule

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkFloatingPointMultiplierDouble(Server#(Tuple3#(Double,Double,RoundMode),Tuple2#(Double,Exception)));
   let _ifc <- mkFloatingPointMultiplier;
   return _ifc;
endmodule

(* synthesize *)
(* options = "-aggressive-conditions" *)
module sysFloatTest(Empty);

   Bool testArith = False;

   Counter#(32) cntErrors <- mkCounter(0);
   PulseWire pwError <- mkPulseWire;

   let divider <- mkFloatingPointDividerDouble;
   FIFOF#(Tuple5#(Double,Double,Double,Exception,RoundMode)) fCheck_div <- mkLFIFOF;

   let sqrter <- mkFloatingPointSquareRooterDouble;
   FIFOF#(Tuple4#(Double,Double,Exception,RoundMode)) fCheck_sqrt <- mkFIFOF;

   let adder <- mkFloatingPointAdderDouble;
   FIFOF#(Tuple5#(Double,Double,Double,Exception,RoundMode)) fCheck_add <- mkFIFOF;

   let multiplier <- mkFloatingPointMultiplier;
   FIFOF#(Tuple5#(Double,Double,Double,Exception,RoundMode)) fCheck_mul <- mkFIFOF;

   let fmac <- mkFloatingPointFusedMultiplyAccumulateDouble;
   FIFOF#(Tuple6#(Maybe#(Double),Double,Double,Double,Exception,RoundMode)) fCheck_fmac <- mkFIFOF;

   function Action testDividePipeRaw(Bit#(64) n, Bit#(64) d, Bit#(64) q, Bit#(5) e, RoundMode rmode);
      action
	 Double nn = unpack(n);
	 Double dd = unpack(d);
	 Double qq = unpack(q);
	 Exception ee = unpack(e);

	 divider.request.put(tuple3(nn,dd,rmode));
	 fCheck_div.enq(tuple5(nn,dd,qq,ee,rmode));
      endaction
   endfunction

   function Action testDividePipe(Real n, Real d);
      action
	 Double nn = fromReal(n);
	 Double dd = fromReal(d);
	 match {.qq, .exc} = divFP(nn, dd, defaultValue);
	 Double qq2 = qnan;

	 if (isNaN(qq) || isInfinity(qq)) begin
	    qq2 = qq;
	 end
	 else begin
	    qq2 = fromReal(n / d);
	 end

	 divider.request.put(tuple3(nn,dd,defaultValue));
	 fCheck_div.enq(tuple5(nn,dd,qq,unpack(0),defaultValue));
      endaction
   endfunction

   function Action testSqrtPipeRaw(Bit#(64) a, Bit#(64) r, Bit#(5) e, RoundMode rmode);
      action
	 Double aa = unpack(a);
	 Double rr = unpack(r);
	 Exception ee = unpack(e);

	 sqrter.request.put(tuple2(aa,rmode));
	 fCheck_sqrt.enq(tuple4(aa,rr,ee,rmode));
      endaction
   endfunction

   function Action testSqrtPipe(Real a);
      action
	 Double b = fromReal(a);
	 Double s = (a < 0) ? qnan() : fromReal(sqrt(a));

	 sqrter.request.put(tuple2(b,defaultValue));
	 fCheck_sqrt.enq(tuple4(b,s,unpack(0),defaultValue));
      endaction
   endfunction

   function Action testAdderPipeRaw(Bit#(64) a, Bit#(64) b, Bit#(64) s, Bit#(5) e, RoundMode rmode);
      action
	 Double aa = unpack(a);
	 Double bb = unpack(b);
	 Double ss = unpack(s);
	 Exception ee = unpack(e);
	 adder.request.put(tuple3(aa,bb,rmode));
	 fCheck_add.enq(tuple5(aa,bb,ss,ee,rmode));
      endaction
   endfunction

   function Action testMultiplierPipeRaw(Bit#(64) a, Bit#(64) b, Bit#(64) p, Bit#(5) e, RoundMode rmode);
      action
	 Double aa = unpack(a);
	 Double bb = unpack(b);
	 Double pp = unpack(p);
	 Exception ee = unpack(e);
	 multiplier.request.put(tuple3(aa,bb,rmode));
	 fCheck_mul.enq(tuple5(aa,bb,pp,ee,rmode));
      endaction
   endfunction

   function Action testFMACRaw(Maybe#(Bit#(64)) a, Bit#(64) b, Bit#(64) c, Bit#(64) r, Bit#(5) e, RoundMode rmode);
      action
	 Maybe#(Double) aa = a matches tagged Valid .a_ ? (tagged Valid unpack(a_)) : tagged Invalid;
	 Double bb = unpack(b);
	 Double cc = unpack(c);
	 Double rr = unpack(r);
	 Exception ee = unpack(e);
	 fmac.request.put(tuple4(aa,bb,cc,rmode));
	 fCheck_fmac.enq(tuple6(aa,bb,cc,rr,ee,rmode));
      endaction
   endfunction

   function Action testFMACAddRaw(Bit#(64) a, Bit#(64) b, Bit#(64) r, Bit#(5) e, RoundMode rmode);
      action
	 testFMACRaw(tagged Valid a,b,pack(Double'(one(False))),r,e,rmode);
      endaction
   endfunction

   function Action testFMACMultiplyRaw(Bit#(64) b, Bit#(64) c, Bit#(64) r, Bit#(5) e, RoundMode rmode);
      action
	 testFMACRaw(tagged Invalid,b,c,r,e,rmode);
      endaction
   endfunction

   function Action test_int32_to_float64(Bit#(32) a, Bit#(64) b);
      action
	 Int#(32) i = unpack(a);
	 Double d = unpack(b);
	 match {.r, .exc} = Tuple2#(Double,Exception)'(vFixedToFloat(i, UInt#(5)'(0), defaultValue));
	 if (d != r) begin
	    $display("convert %8x", i, " to float ", fshow(r), " (", pack(exc), "), expected ", fshow(d));
	    pwError.send;
	 end
	 else begin
	    $display("convert %8x", i, " to float ", fshow(r), " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   function Action test_int32_to_float32(Bit#(32) a, Bit#(32) b, RoundMode rmode);
      action
	 Int#(32) i = unpack(a);
	 Float d = unpack(b);
	 match {.r, .exc} = Tuple2#(Float,Exception)'(vFixedToFloat(i, UInt#(5)'(0), rmode));
	 if (d != r) begin
	    $display("convert %8x", i, " to float ", fshow(r), " ('b%b", pack(exc), "), expected ", fshow(d));
	    pwError.send;
	 end
	 else begin
	    $display("convert %8x", i, " to float ", fshow(r), " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   function Action test_float32_to_int32(Bit#(32) a, Bit#(32) b, RoundMode rmode);
      action
	 Float f = unpack(a);
	 Int#(32) i = unpack(b);
	 match {.r, .exc} = Tuple2#(Int#(32),Exception)'(vFloatToFixed(UInt#(5)'(0), f, rmode));
	 if (i != r) begin
	    $display("convert ", fshow(f), " to int %8x", r, " ('b%b", pack(exc), "), expected %8x", i);
	    pwError.send;
	 end
	 else begin
	    $display("convert ", fshow(f), " to int %8x", r, " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   function Action test_float64_to_int32(Bit#(64) a, Bit#(32) b, RoundMode rmode);
      action
	 Double d = unpack(a);
	 Int#(32) i = unpack(b);
	 match {.r, .exc} = Tuple2#(Int#(32),Exception)'(vFloatToFixed(UInt#(5)'(0), d, rmode));
	 if (i != r) begin
	    $display("convert ", fshow(d), " to int %8x", r, " ('b%b", pack(exc), "), expected %8x", i);
	    pwError.send;
	 end
	 else begin
	    $display("convert ", fshow(d), " to int %8x", r, " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   function Action test_float64_to_int64(Bit#(64) a, Bit#(64) b, RoundMode rmode);
      action
	 Double d = unpack(a);
	 Int#(64) i = unpack(b);
	 match {.r, .exc} = Tuple2#(Int#(64),Exception)'(vFloatToFixed(UInt#(6)'(0), d, rmode));
	 if (i != r) begin
	    $display("convert ", fshow(d), " to int %16x", r, " ('b%b", pack(exc), "), expected %8x", i);
	    pwError.send;
	 end
	 else begin
	    $display("convert ", fshow(d), " to int %16x", r, " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   function Action test_float64_to_uint64(Bit#(64) a, Bit#(64) b, RoundMode rmode);
      action
	 Double d = unpack(a);
	 UInt#(64) i = unpack(b);
	 match {.r, .exc} = Tuple2#(UInt#(64),Exception)'(vFloatToFixed(UInt#(6)'(0), d, rmode));
	 if (i != r) begin
	    $display("convert ", fshow(d), " to int %16x", r, " ('b%b", pack(exc), "), expected %8x", i);
	    pwError.send;
	 end
	 else begin
	    $display("convert ", fshow(d), " to int %16x", r, " ('b%b", pack(exc), ")");
	 end
      endaction
   endfunction

   Stmt div_test =
   seq
      //////////////////////////////
      // mkFloatingPointDivider

      testDividePipeRaw('h40D03A98FB4D2934, 'hF64FFFFFFFFFFFF2, 'h8A703A98FB4D293B, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3FDFFFFFFFFE2000, 'h3FD0CB1C7EB24E54, 'h3FFE7CF8276BCD83, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h700FFC0000FFFFFF, 'hBFCFFFF7FFFFFFFF, 'hF02FFC0800020000, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3FE4000000000010, 'hBFB56EEB12035CFF, 'hC01DDC30615408D9, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hBFDFFFFF8000000E, 'h48007FFFFFFFFFFF, 'hB7CF07C1745D1755, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h200FFFFFFE000020, 'h0000000000000001, 'h632FFFFFFE000020, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h41F0097A1031666C, 'h3FEFFFFFFF0000FE, 'h41F0097A10B1B1BD, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC7F87775DF80840B, 'h40A0000003FFF800, 'hC7487775D962B2D0, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC3DFFFEFFFFFFFFA, 'hC3DD5478CA7C0277, 'h3FF174D79C098BC0, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC7FEAB8A54459C9A, 'h000FFFFFFFFFFFFF, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hC0E946F6B22AE21E, 'h480216620D990B99, 'hB8D65C29BA098C86, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hBFD0000000000001, 'h3FC6C01280B21CD2, 'hBFF68155C8C6875D, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hB81FFFFFFF801FFE, 'hC1DFFFC00000001F, 'h3630002000000FF0, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC29FF80020000000, 'h000FFFFFFFFFFFFE, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hC3E2008000000000, 'h402000007FFFEFFE, 'hC3B2007F6FFC1683, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hFFDFC007FFFFFFFF, 'hC800000020000007, 'h77CFC007C07FF070, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h43C0000008000000, 'hBCA007FFFFDFFFFF, 'hC70FF0080C39C330, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h4240000000200400, 'h402C0000FFFFFFFF, 'h42024923EB3EBC2C, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h381FFFFFFFFBF7FF, 'h43B0007FFFFFFFFE, 'h345FFF0007FBB825, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hBFB07FDFFFFFFFFE, 'h41D0000100000008, 'hBDD07FDEF8021076, 'b00001, Rnd_Nearest_Even);

      testDividePipeRaw('hA6FFFFFFFF7FFDFF, 'hC1CDE857A9DC8F5E, 'h25211E911819C833, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC1CE000000001000, 'h402FFFE001FFFFFE, 'hC18E001DFE3E0C60, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC00FFFFFE0800000, 'h000FFFFFFFFFFFFE, 'hFFEFFFFFE0800004, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3800CC3FDF1CF190, 'h3FCFFFFFFFC00080, 'h3820CC3FDF3E89CD, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC0040B081A7B3E03, 'hBF5B70EA7914093F, 'h40975F79B1B88272, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h47F000008000007E, 'hBFEFFFFFFFFFFFF0, 'hC7F0000080000086, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h41D00080000001FF, 'hBFF0000020001FFF, 'hC1D0007FDFFEE23F, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hBE7FFFFFFFFF7FFA, 'hFFD0000000020FFF, 'h0000000020000000, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('hF76FFFFFFFE00FFE, 'h3CAFFFFFFF8007FE, 'hFAB0000000300400, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC60003FFFEFFFFFE, 'h41C003FFFFDFFFFF, 'hC42FFFFFFE406FE2, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hB800800000000000, 'h3FFFFFFFFFF7FFFC, 'hB7F0800000042002, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC0E93E0145DC5600, 'h3E80080001FFFFFF, 'hC25931688E6EF177, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h41FFFFFF80020000, 'h3FE0000000000001, 'h420FFFFF8001FFFE, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3D60000000000804, 'hBFBB1B9120451D27, 'hBD92E33BFC126289, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hBFF0E3BAF09C0997, 'h3FEFFFFFFFFFFFFE, 'hBFF0E3BAF09C0998, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h404020000FFFFFFF, 'h3FF3792D39C17AA6, 'h403A7F6D1BA6715B, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC110080000000200, 'h41FFFFFFF0000000, 'hBF00080008040204, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h7E5FFFFFFFFE001F, 'h3FF0000000000001, 'h7E5FFFFFFFFE001D, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3F1FFFFFFF000008, 'h43EFFFEFFFFFF000, 'h3B200007FF8407C6, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h41FFFFFFFFF7FFDE, 'h7FD0000000000400, 'h021FFFFFFFF7F7DE, 'b00001, Rnd_Nearest_Even);

      testDividePipeRaw('h0000042000000000, 'h80283FFFFFFFFFFF, 'hBF35C5F02A3A0FD7, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3FD040000000007F, 'h0000000000000001, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hBDF0000018000000, 'h0000000001F80000, 'hFF80410428A28A29, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('hC00000000002007F, 'h00010003FFFFFFFE, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hBEB707FA38497790, 'h0003FBFFFFFFFFFF, 'hFEB71F19519B12A8, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3FA080000000003F, 'h000000000000001F, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h000FFFFFFFFFFFFF, 'h3CB0000000000001, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h000FFFFFFFFFFFFE, 'h3CB0000000000002, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hBFCAF02675DC1DEF, 'h8000000000000005, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h0010000000000001, 'h3CAFFFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h001FFFFFFFFFFFFF, 'h3CA0000000000001, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h001FFFFFFFFFFFFE, 'h3CA0000000000001, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3800000043FFFFFF, 'h04BFFFFF78000244, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3CA0000000000001, 'h001FFFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3CAFFFFFFFFFFFFF, 'h0010000000000001, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hBE907FFFFFFEFFFE, 'h80000000003E0F84, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3CAFFFFFFFFFFFFE, 'h0010000000000001, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h369F64D478EAFC3F, 'h06204F153E0138A9, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h0003818C4C2AD04D, 'h3CD24111B0A5B490, 'b00001, Rnd_Nearest_Even);
      testDividePipeRaw('h3CA000003FFFFFFF, 'h0001C394CA4F8A3E, 'h7CB224054D2088BB, 'b00001, Rnd_Nearest_Even);

      testDividePipeRaw('h7FD0001FFFDFFFFF, 'h3FD0000000000000, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hFFEFDFEF804426F1, 'hBFE0000000000001, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hC02FFFFDFFFFFF7F, 'h0020000007FFFC00, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000001, 'h4340000000000000, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000001, 'hC340000000000000, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h7FDFF80000000008, 'hBFD0000000000000, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h7FE13830B6549038, 'h3FE0000000000000, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h401080000000007F, 'h8010000000000001, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h40240000000FFFFF, 'h002000000000000E, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h4020090000000000, 'h00200007FFFFFF00, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hFFD56529A98140B6, 'hBFD0000000000001, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hC02FFFFFF7BFFFFF, 'h802C486F59A2857F, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h7FD020000000001F, 'hBFD0000000000000, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h7FD000020003FFFF, 'hBFD0000000000001, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hFFDFFFFFFFFFBFFD, 'hBFDF9E5BF16F8E94, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('hFFD82591FF34E5C3, 'h3FD0000000000000, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h400FFFFFFFFFFFFF, 'h000FFFFFFFFFFFFF, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h400FFFFFFFFFFFFF, 'h000FFFFFFFFFFFFE, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h400FFFFFFFFFFFFF, 'h800FFFFFFFFFFFFF, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);
      testDividePipeRaw('h400FFFFFFFFFFFFF, 'h800FFFFFFFFFFFFE, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);

      testDividePipeRaw('h0010000000000001, 'h4340000000000000, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000001, 'hC340000000000000, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h3E7FFFFC000001FF, 'h7FE0000000000000, 'h000000000FFFFE00, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0020000040000200, 'h4340000000000000, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h8010000000000001, 'h4340000000000000, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h8010000000000001, 'hC340000000000000, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('hBF4080000000000F, 'h7FE0000000000000, 'h8000010800000000, 'b00011, Rnd_Nearest_Even);

      testDividePipeRaw('h0000000000000001, 'h3FD0000000000000, 'h0000000000000004, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3FE0000000000000, 'h0000000000000002, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h3FF0000000000000, 'h0000000000000001, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'h4000000000000000, 'h0000000000000000, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hBFD0000000000000, 'h8000000000000004, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hBFE0000000000000, 'h8000000000000002, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hBFF0000000000000, 'h8000000000000001, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0000000000000001, 'hC000000000000000, 'h8000000000000000, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFF, 'h400FFFFFFFFFFFFE, 'h0004000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFF, 'h401FFFFFFFFFFFFE, 'h0002000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFF, 'hC00FFFFFFFFFFFFE, 'h8004000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFF, 'hC01FFFFFFFFFFFFE, 'h8002000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFE, 'h4000000000000000, 'h0007FFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h000FFFFFFFFFFFFE, 'hC000000000000000, 'h8007FFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000000, 'h4010000000000000, 'h0004000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000000, 'h4340000000000000, 'h0000000000000000, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000000, 'hC010000000000000, 'h8004000000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000000, 'hC040000000000000, 'h8000800000000000, 'b00000, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000000, 'hC340000000000000, 'h8000000000000000, 'b00011, Rnd_Nearest_Even);
      testDividePipeRaw('h0010000000000001, 'h4010000000000001, 'h0004000000000000, 'b00000, Rnd_Nearest_Even);

      while (fCheck_div.notEmpty)
	 noAction;
   endseq;

   let div_fsm <- mkFSM(div_test);

   Stmt sqrt_test =
   seq
      //////////////////////////////
      // mkFloatingPointSquareRooter

      testSqrtPipeRaw('h0000000000000001, 'h1E60000000000000, 'b00000, Rnd_Nearest_Even);
      testSqrtPipeRaw('h43EE1FFFFFFFFFFF, 'h41EF0C60A033A7B2, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h000FFFFFFFFFFFFF, 'h1FFFFFFFFFFFFFFF, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h000FFFFFFFFFFFFE, 'h1FFFFFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h419087FFFFFFFFFF, 'h40C04371D9AB72FB, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h0020000000000000, 'h2006A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h37E0000000000000, 'h3BE6A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3800000000000000, 'h3BF6A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h7FEFFFFFF07FFFFE, 'h5FEFFFFFF83FFFFE, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3EA2000200000000, 'h3F48000155554BDA, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h37FC000004000000, 'h3BF52A7FAB560208, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3CA0000000000000, 'h3E46A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h37E725BD48E809C9, 'h3BEB3753ECC5F0BF, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3FC0000000000000, 'h3FD6A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3FE0000000000000, 'h3FE6A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h40207FFFFFFFFEFF, 'h4006FA6EA162D03D, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h4000000000000000, 'h3FF6A09E667F3BCD, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h000FFFFFFFFF8800, 'h1FFFFFFFFFFF8800, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h3DE0000040040000, 'h3EE6A09E93C34C80, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h4020000000000000, 'h4006A09E667F3BCD, 'b00001, Rnd_Nearest_Even);

      testSqrtPipeRaw('h4050000007FFFFFF, 'h4020000003FFFFFF, 'b00001, Rnd_Nearest_Even);

      testSqrtPipeRaw('h0000000000000001, 'h1E60000000000000, 'b00000, Rnd_Nearest_Even);
      testSqrtPipeRaw('h000048D4DBC1D51A, 'h1FD1117A47FB2FE2, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h000004000FFFFFFF, 'h1FB0001FFFDFFE40, 'b00001, Rnd_Nearest_Even);
      testSqrtPipeRaw('h0000040000000800, 'h1FB0000000100000, 'b00001, Rnd_Nearest_Even);

      testSqrtPipeRaw('h0000000000000001, 'h1E60000000000000, 'b00000, Rnd_Zero);

      testSqrtPipeRaw('h0000000000000001, 'h1E60000000000000, 'b00000, Rnd_Minus_Inf);
      testSqrtPipeRaw('h0000007FFEFFFFFF, 'h1F96A087C5D56E52, 'b00001, Rnd_Minus_Inf);

      testSqrtPipeRaw('h0000000000000001, 'h1E60000000000000, 'b00000, Rnd_Plus_Inf);
      testSqrtPipeRaw('h0001000000000000, 'h1FE0000000000000, 'b00000, Rnd_Plus_Inf);

      while (fCheck_sqrt.notEmpty)
	 noAction;
   endseq;

   let sqrt_fsm <- mkFSM(sqrt_test);

   Stmt add_test =
   seq
      //////////////////////////////
      // mkFloatingPointAdder

      testAdderPipeRaw('h3FD040001FFFFFFE, 'h412FFFFFC000000F, 'h4130000021000087, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('hBF72D689E3FFEFA8, 'h3FD0000000000001, 'h3FCF694BB0E00085, 'b00001, Rnd_Nearest_Even);

      testAdderPipeRaw('hBF72D689E3FFEFA8, 'h3FD0000000000001, 'h3FCF694BB0E00085, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('hBFDA469AC331DBEE, 'h41F00000000000C0, 'h41EFFFFFFFF2DE33, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h0010000000000000, 'h0010000000000001, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h0010000000000001, 'h0010000000000002, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h001FFFFFFFFFFFFF, 'h0020000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h001FFFFFFFFFFFFE, 'h001FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h000000000FFFFFEF, 'h810DA0D6D3B07227, 'h810DA0D6D3B05227, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('h00140000000007FF, 'h800FFFFFFFFFFFFE, 'h0004000000000801, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h8010000000000000, 'h800FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h8010000000000001, 'h8010000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h801FFFFFFFFFFFFF, 'h801FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h801FFFFFFFFFFFFE, 'h801FFFFFFFFFFFFD, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h802FFFFFFFFFFFFF, 'h802FFFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('h0000000000000001, 'h801A6C96CCFE161E, 'h801A6C96CCFE161D, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h000FFFFFFFFFFFFF, 'h0010000000000000, 'h001FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h000FFFFFFFFFFFFF, 'h0010000000000001, 'h0020000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h000FFFFFFFFFFFFF, 'h001FFFFFFFFFFFFF, 'h0027FFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h000FFFFFFFFFFFFF, 'h001FFFFFFFFFFFFE, 'h0027FFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('hF7B3E0E3298BB93F, 'h7900000000080000, 'h78FFFFFEC201CD67, 'b00001, Rnd_Nearest_Even);
      testAdderPipeRaw('h000FFFFFFFFFFFFF, 'h801FFFFFFFEFFDFF, 'h800FFFFFFFEFFE00, 'b00000, Rnd_Nearest_Even);

      testAdderPipeRaw('h3CA0000000000000, 'hBCA0000000000001, 'hB960000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3CA0000000000001, 'hBCA0000000000000, 'h3960000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3CAFFFFFFFFFFFFF, 'hBCAFFFFFFFFFFFFE, 'h3960000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3CAFFFFFFFFFFFFE, 'hBCAFFFFFFFFFFFFF, 'hB960000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FD0000000000000, 'hBFD0000000000001, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FD0000000000001, 'hBFD0000000000000, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFF, 'hBFDFFFFFFFFFFFFE, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFF, 'hBFE0000000000000, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFF, 'hBFE0000000000001, 'hBCA8000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFE, 'hBFDFFFFFFFFFFFFF, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFE, 'hBFE0000000000000, 'hBCA0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FDFFFFFFFFFFFFE, 'hBFE0000000000001, 'hBCB0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000000, 'hBFE0000000020020, 'hBDB0010000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000000, 'hBFDFFFFFFFFFFFFF, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000000, 'hBFDFFFFFFFFFFFFE, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000000, 'hBFE0000000000001, 'hBCA0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000001, 'hBFDFFFFFFFFFFFFF, 'h3CA8000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000001, 'hBFDFFFFFFFFFFFFE, 'h3CB0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FE0000000000001, 'hBFE0000000000000, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);
      testAdderPipeRaw('h3FEFFFFFFFFFFFFF, 'hBFEFFFFFFFFFFFFE, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);

      while (fCheck_add.notEmpty)
	 noAction;
   endseq;

   let add_fsm <- mkFSM(add_test);

   Stmt mul_test =
   seq
      //////////////////////////////
      // mkFloatingPointMultiplier

      testMultiplierPipeRaw('h41DFFFFFFFFFFFF8, 'h7FD0040000004000, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testMultiplierPipeRaw('hDB9FFFFFFFFC0800, 'h3CAFFFFBFFFF7FFF, 'hD85FFFFBFFFB87FF, 'b00001, Rnd_Nearest_Even);
      testMultiplierPipeRaw('hBF708001FFFFFFFF, 'h0000000000000001, 'h8000000000000000, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('hC0110938445D0EB2, 'h8000040000003FFE, 'h0000110938456D9A, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('hBFFFFDFFFFFFFFDF, 'h00050F0BDB91CE61, 'h800A1D75D5A82A7E, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FE0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFF, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h4000000000000000, 'h001FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);

      testMultiplierPipeRaw('h0000000000000001, 'h3FFFFFFFFBFC0000, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FE0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FF0000000000000, 'h0000000000000001, 'b00000, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FF0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FFFFFFFFFFFFFFF, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FFFFFFFFFFFFFFE, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h3FFFFF0003FFFFFF, 'h8000000000000001, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'h3FF3A4B6AD8EBB62, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h3CAFFFFE00000100, 'h800FFFFFFFFFFFFF, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'hBFE0000000000001, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'hBFF0000000000000, 'h8000000000000001, 'b00000, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'hBFF0000000000001, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'hBFFFFFFFFFFFFFFF, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0000000000000001, 'hBFFFFFFFFFFFFFFE, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'hBCA2CB063D0F8F52, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFF, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFE, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h3FDFFFFFFFFFFFFE, 'h0007FFFFFFFFFFFF, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h3FEFFFFFFFFFFFFF, 'h000FFFFFFFFFFFFF, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h000FFFFFFFFFFFFF, 'h4000000000000000, 'h001FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);
      testMultiplierPipeRaw('hBFBA4A1610C1E49F, 'hC03FFFFFFF800002, 'h400A4A161058BC48, 'b00001, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h0010000000000001, 'h3CA0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);

      testMultiplierPipeRaw('h37F20000001FFFFF, 'h84BD87FE2EA0C84F, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testMultiplierPipeRaw('h3C96000000000000, 'h001E000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);

      testMultiplierPipeRaw('hB7E00010007FFFFE, 'h000FFFFFFFFFFFFE, 'h8000000000000001, 'b00011, Rnd_Minus_Inf);

      while (fCheck_mul.notEmpty)
	 noAction;
   endseq;

   let mul_fsm <- mkFSM(mul_test);

   Stmt fmac_test =
   seq
      //////////////////////////////
      // mkFloatingPointFusedMultiplyAccumulate

      testFMACAddRaw('h3FD040001FFFFFFE, 'h412FFFFFC000000F, 'h4130000021000087, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('hBF72D689E3FFEFA8, 'h3FD0000000000001, 'h3FCF694BB0E00085, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('hBF72D689E3FFEFA8, 'h3FD0000000000001, 'h3FCF694BB0E00085, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('hBFDA469AC331DBEE, 'h41F00000000000C0, 'h41EFFFFFFFF2DE33, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h0010000000000000, 'h0010000000000001, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h0010000000000001, 'h0010000000000002, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h001FFFFFFFFFFFFF, 'h0020000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h001FFFFFFFFFFFFE, 'h001FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h000000000FFFFFEF, 'h810DA0D6D3B07227, 'h810DA0D6D3B05227, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('h00140000000007FF, 'h800FFFFFFFFFFFFE, 'h0004000000000801, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h8010000000000000, 'h800FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h8010000000000001, 'h8010000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h801FFFFFFFFFFFFF, 'h801FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h801FFFFFFFFFFFFE, 'h801FFFFFFFFFFFFD, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h802FFFFFFFFFFFFF, 'h802FFFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('h0000000000000001, 'h801A6C96CCFE161E, 'h801A6C96CCFE161D, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h000FFFFFFFFFFFFF, 'h0010000000000000, 'h001FFFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h000FFFFFFFFFFFFF, 'h0010000000000001, 'h0020000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h000FFFFFFFFFFFFF, 'h001FFFFFFFFFFFFF, 'h0027FFFFFFFFFFFF, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h000FFFFFFFFFFFFF, 'h001FFFFFFFFFFFFE, 'h0027FFFFFFFFFFFE, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('hF7B3E0E3298BB93F, 'h7900000000080000, 'h78FFFFFEC201CD67, 'b00001, Rnd_Nearest_Even);
      testFMACAddRaw('h000FFFFFFFFFFFFF, 'h801FFFFFFFEFFDFF, 'h800FFFFFFFEFFE00, 'b00000, Rnd_Nearest_Even);

      testFMACAddRaw('h3CA0000000000000, 'hBCA0000000000001, 'hB960000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3CA0000000000001, 'hBCA0000000000000, 'h3960000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3CAFFFFFFFFFFFFF, 'hBCAFFFFFFFFFFFFE, 'h3960000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3CAFFFFFFFFFFFFE, 'hBCAFFFFFFFFFFFFF, 'hB960000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FD0000000000000, 'hBFD0000000000001, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FD0000000000001, 'hBFD0000000000000, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFF, 'hBFDFFFFFFFFFFFFE, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFF, 'hBFE0000000000000, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFF, 'hBFE0000000000001, 'hBCA8000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFE, 'hBFDFFFFFFFFFFFFF, 'hBC90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFE, 'hBFE0000000000000, 'hBCA0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FDFFFFFFFFFFFFE, 'hBFE0000000000001, 'hBCB0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000000, 'hBFE0000000020020, 'hBDB0010000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000000, 'hBFDFFFFFFFFFFFFF, 'h3C90000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000000, 'hBFDFFFFFFFFFFFFE, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000000, 'hBFE0000000000001, 'hBCA0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000001, 'hBFDFFFFFFFFFFFFF, 'h3CA8000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000001, 'hBFDFFFFFFFFFFFFE, 'h3CB0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FE0000000000001, 'hBFE0000000000000, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACAddRaw('h3FEFFFFFFFFFFFFF, 'hBFEFFFFFFFFFFFFE, 'h3CA0000000000000, 'b00000, Rnd_Nearest_Even);

      testFMACMultiplyRaw('h41DFFFFFFFFFFFF8, 'h7FD0040000004000, 'h7FF0000000000000, 'b00101, Rnd_Nearest_Even);
      testFMACMultiplyRaw('hDB9FFFFFFFFC0800, 'h3CAFFFFBFFFF7FFF, 'hD85FFFFBFFFB87FF, 'b00001, Rnd_Nearest_Even);
      testFMACMultiplyRaw('hBF708001FFFFFFFF, 'h0000000000000001, 'h8000000000000000, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('hC0110938445D0EB2, 'h8000040000003FFE, 'h0000110938456D9A, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('hBFFFFDFFFFFFFFDF, 'h00050F0BDB91CE61, 'h800A1D75D5A82A7E, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FE0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFF, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h4000000000000000, 'h001FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);

      testFMACMultiplyRaw('h0000000000000001, 'h3FFFFFFFFBFC0000, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FE0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FF0000000000000, 'h0000000000000001, 'b00000, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FF0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FFFFFFFFFFFFFFF, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FFFFFFFFFFFFFFE, 'h0000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h3FFFFF0003FFFFFF, 'h8000000000000001, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'h3FF3A4B6AD8EBB62, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h3CAFFFFE00000100, 'h800FFFFFFFFFFFFF, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'hBFE0000000000001, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'hBFF0000000000000, 'h8000000000000001, 'b00000, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'hBFF0000000000001, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'hBFFFFFFFFFFFFFFF, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0000000000000001, 'hBFFFFFFFFFFFFFFE, 'h8000000000000002, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'hBCA2CB063D0F8F52, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFF, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h3CAFFFFFFFFFFFFE, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h3FDFFFFFFFFFFFFE, 'h0007FFFFFFFFFFFF, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h3FEFFFFFFFFFFFFF, 'h000FFFFFFFFFFFFF, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h000FFFFFFFFFFFFF, 'h4000000000000000, 'h001FFFFFFFFFFFFE, 'b00000, Rnd_Nearest_Even);
      testFMACMultiplyRaw('hBFBA4A1610C1E49F, 'hC03FFFFFFF800002, 'h400A4A161058BC48, 'b00001, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h0010000000000001, 'h3CA0000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);

      testFMACMultiplyRaw('h37F20000001FFFFF, 'h84BD87FE2EA0C84F, 'h8000000000000001, 'b00011, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h3C96000000000000, 'h001E000000000001, 'h0000000000000001, 'b00011, Rnd_Nearest_Even);

      testFMACMultiplyRaw('hB7E00010007FFFFE, 'h000FFFFFFFFFFFFE, 'h8000000000000001, 'b00011, Rnd_Minus_Inf);

      testFMACAddRaw('hC00FFFFFFFFFFFFF, 'h400FFFFFFFFFFFFF, 'h0000000000000000, 'b00000, Rnd_Nearest_Even);

      testFMACAddRaw('h8000000000000000, 'h8000000000000000, 'h8000000000000000, 'b00000, Rnd_Nearest_Even);

      testFMACMultiplyRaw('h0000000000000000, 'hC1D47E51E1AF0384, 'h8000000000000000, 'b00000, Rnd_Nearest_Even);

      testFMACMultiplyRaw('h0000000000000000, 'h8010010000000007, 'h8000000000000000, 'b00000, Rnd_Nearest_Even);
      testFMACMultiplyRaw('h7FEFFFFFFE7FFFFF, 'hC1C67808EFB5EC47, 'hFFF0000000000000, 'b00101, Rnd_Nearest_Even);

      testFMACMultiplyRaw('hA010002004000000, 'h0010000000000001, 'h8000000000000001, 'b00011, Rnd_Minus_Inf);

      while (fCheck_fmac.notEmpty)
	 noAction;
   endseq;

   let fmac_fsm <- mkFSM(fmac_test);

   Stmt cvt_test =
   seq
      //////////////////////////////
      // FloatFixedCVT

      test_int32_to_float64('h01FDFFF5, 'h417FDFFF50000000);
      test_int32_to_float64('h0000179D, 'h40B79D0000000000);
      test_int32_to_float64('h00080203, 'h4120040600000000);
      test_int32_to_float64('hFFEF1FFD, 'hC130E00300000000);
      test_int32_to_float64('h00000001, 'h3FF0000000000000);
      test_int32_to_float64('h02000011, 'h4180000088000000);
      test_int32_to_float64('hEA15F736, 'hC1B5EA08CA000000);
      test_int32_to_float64('h00000002, 'h4000000000000000);
      test_int32_to_float64('hFFFF0001, 'hC0EFFFE000000000);
      test_int32_to_float64('hFFFE65FD, 'hC0F9A03000000000);
      test_int32_to_float64('h00000004, 'h4010000000000000);
      test_int32_to_float64('hFBFF0001, 'hC19003FFFC000000);
      test_int32_to_float64('h0A047A71, 'h41A408F4E2000000);
      test_int32_to_float64('h00000008, 'h4020000000000000);
      test_int32_to_float64('hC00007BD, 'hC1CFFFFC21800000);
      test_int32_to_float64('hFFFD55D8, 'hC105514000000000);
      test_int32_to_float64('h00000010, 'h4030000000000000);
      test_int32_to_float64('hFE00003D, 'hC17FFFFC30000000);
      test_int32_to_float64('h00088907, 'h4121120E00000000);
      test_int32_to_float64('h00000020, 'h4040000000000000);
      test_int32_to_float64('h00000000, 'h0000000000000000);

      test_int32_to_float32('h01FDFFF5, 'h4BFEFFFA, defaultValue);
      test_int32_to_float32('hC000001D, 'hCE800000, defaultValue);
      test_int32_to_float32('h7FFFFFFF, 'h4F000000, Rnd_Nearest_Even);

      test_float32_to_int32('h3F800000, 'h00000001, Rnd_Zero);
      test_float32_to_int32('h3FC00000, 'h00000001, Rnd_Zero);
      test_float32_to_int32('hBFF80FFF, 'hFFFFFFFF, Rnd_Zero);
      test_float32_to_int32('hBF800000, 'hFFFFFFFF, Rnd_Zero);
      test_float32_to_int32('hBF800001, 'hFFFFFFFF, Rnd_Zero);
      test_float32_to_int32('hC0000000, 'hFFFFFFFE, Rnd_Zero);
      test_float32_to_int32('hCF000000, 'h80000000, Rnd_Zero);

      test_float64_to_int32('hC1E0000000000001, 'h80000000, Rnd_Zero);
      test_float64_to_int32('h0000000000000001, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h000FFFFFFFFFFFFF, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h8020007FFDFFFFFE, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h000FFFFFFFFFFFFE, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h0010000000000000, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h0010000000000001, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h001FFFFFFFFFFFFF, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h001FFFFFFFFFFFFE, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h0020000000000000, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h0020000000000001, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h002FFFFFFFFFFFFF, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h000000003F7FFFFF, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h002FFFFFFFFFFFFE, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h800E879FE2F7F867, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h8018567C2C403D88, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h00100000003FFEFF, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h800FDFFBFFFFFFFE, 'h00000000, Rnd_Zero);
      test_float64_to_int32('h808000FFFFFFFFFF, 'h00000000, Rnd_Zero);

      test_float64_to_int64('h0000000000000001, 'h0000000000000000, Rnd_Zero);

      test_float64_to_uint64('h0000000000000001, 'h0000000000000000, Rnd_Zero);
   endseq;

   let cvt_fsm <- mkFSM(cvt_test);

   Stmt test =
   seq
      div_fsm.start;
      div_fsm.waitTillDone;
      sqrt_fsm.start;
      sqrt_fsm.waitTillDone;
      add_fsm.start;
      add_fsm.waitTillDone;
      mul_fsm.start;
      mul_fsm.waitTillDone;
      fmac_fsm.start;
      fmac_fsm.waitTillDone;
      cvt_fsm.start;
      cvt_fsm.waitTillDone;

      action
	 if (cntErrors.value != 0) begin
	    $display("%d error(s) found.", cntErrors.value);
	 end
      endaction

   endseq;

   (* mutually_exclusive = "check_div, check_sqrt, check_add, check_mul, check_fmac" *)
   (* preempts = "error, (check_div, check_sqrt, check_add, check_mul, check_fmac)" *)

   rule error(pwError);
      cntErrors.up;
   endrule

   rule check_div;
      let err = 0;
      match {.nn,.dd,.qq,.ee,.rmode} <- toGet(fCheck_div).get;
      match {.q,.e} <- divider.response.get;

      if ((pack(q) != pack(qq)) || (pack(e) != pack(ee))) begin
	 $display("divide ", fshow(nn), " / ", fshow(dd), " = ", fshow(q), " ('b%b)", pack(e), ", expected ", fshow(qq), " ('b%b)", pack(ee));
	 err = err + 1;
      end
      else begin
	 $display("divide ", fshow(nn), " / ", fshow(dd), " = ", fshow(q), " ('b%b)", pack(e));
      end

      if (testArith) begin
	 match {.q2,.e2} = divFP(nn,dd,rmode);

	 if ((pack(q2) != pack(qq)) || (pack(e2) != pack(ee))) begin
	    $display("divFP ", fshow(nn), " / ", fshow(dd), " = ", fshow(q2), " ('b%b)", pack(e2), ", expected ", fshow(qq), " ('b%b)", pack(ee));
	    err = err + 1;
	 end
	 else begin
	    $display("divFP ", fshow(nn), " / ", fshow(dd), " = ", fshow(q2), " ('b%b)", pack(e2));
	 end
      end

      cntErrors.inc(err);
   endrule

   rule check_sqrt;
      let err = 0;
      match {.aa, .rr, .ee, .rmode} <- toGet(fCheck_sqrt).get;
      match {.r, .e} <- sqrter.response.get;

      if ((pack(r) != pack(rr)) || (pack(e) != pack(ee))) begin
	 $display("sqrter(", fshow(aa), ") = ", fshow(r), " ('b%b)", pack(e), ", expected ", fshow(rr), " ('b%b)", pack(ee));
	 err = err + 1;
      end
      else begin
	 $display("sqrter(", fshow(aa), ") = ", fshow(r), " ('b%b)", pack(e));
      end

      if (testArith) begin
	 match {.r2, .e2} = sqrtFP(aa, rmode);

	 if ((pack(r2) != pack(rr)) || (pack(e2) != pack(ee))) begin
	    $display("sqrtFP(", fshow(aa), ") = ", fshow(r2), " ('b%b)", pack(e2), ", expected ", fshow(rr), " ('b%b)", pack(ee));
	    err = err + 1;
	 end
	 else begin
	    $display("sqrtFP(", fshow(aa), ") = ", fshow(r2), " ('b%b)", pack(e2));
	 end
      end

      cntErrors.inc(err);
   endrule

   rule check_add;
      let err = 0;
      match {.aa, .bb, .ss, .ee, .rmode} <- toGet(fCheck_add).get;
      match {.s, .e} <- adder.response.get;

      if ((pack(s) != pack(ss)) || (pack(e) != pack(ee))) begin
	 $display(fshow(aa), " + ", fshow(bb), " = ", fshow(s), " ('b%b)", pack(e), ", expected ", fshow(ss), " ('b%b)", pack(ee));
	 err = err + 1;
      end
      else begin
	 $display(fshow(aa), " + ", fshow(bb), " = ", fshow(s), " ('b%b)", pack(e));
      end

      if (testArith) begin
	 match {.s2, .e2} = addFP(aa,bb,rmode);

	 if ((pack(s2) != pack(ss)) || (pack(e2) != pack(ee))) begin
	    $display("addFP", fshow(aa), " + ", fshow(bb), " = ", fshow(s2), " ('b%b)", pack(e2), ", expected ", fshow(ss), " ('b%b)", pack(ee));
	    err = err + 1;
	 end
	 else begin
	    $display("addFP", fshow(aa), " + ", fshow(bb), " = ", fshow(s2), " ('b%b)", pack(e2));
	 end
      end

      cntErrors.inc(err);
   endrule

   rule check_mul;
      let err = 0;
      match {.aa, .bb, .pp, .ee, .rmode} <- toGet(fCheck_mul).get;
      match {.p, .e} <- multiplier.response.get;

      if ((pack(p) != pack(pp)) || (pack(e) != pack(ee))) begin
	 $display(fshow(aa), " * ", fshow(bb), " = ", fshow(p), " ('b%b)", pack(e), ", expected ", fshow(pp), " ('b%b)", pack(ee));
	 err = err + 1;
      end
      else begin
	 $display(fshow(aa), " * ", fshow(bb), " = ", fshow(p), " ('b%b)", pack(e));
      end

      if (testArith) begin
	 match {.p2, .e2} = multFP(aa,bb,rmode);

	 if ((pack(p2) != pack(pp)) || (pack(e2) != pack(ee))) begin
	    $display(fshow(aa), " * ", fshow(bb), " = ", fshow(p2), " ('b%b)", pack(e2), ", expected ", fshow(pp), " ('b%b)", pack(ee));
	    err = err + 1;
	 end
	 else begin
	    $display(fshow(aa), " * ", fshow(bb), " = ", fshow(p2), " ('b%b)", pack(e2));
	 end
      end

      cntErrors.inc(err);
   endrule

   rule check_fmac;
      match {.aa, .bb, .cc, .rr, .ee, .rmode} <- toGet(fCheck_fmac).get;
      match {.r, .e} <- fmac.response.get;

      if ((pack(r) != pack(rr)) || (pack(ee) != pack(e))) begin
	 if (aa matches tagged Valid .aa_) begin
	    $display(fshow(aa_), " + ", fshow(bb), " * ", fshow(cc), " = ", fshow(r), " ('b%b)", pack(e), ", expected ", fshow(rr), " ('b%b)", pack(ee));
	    cntErrors.up;
	 end
	 else begin
	    $display("zero + ", fshow(bb), " * ", fshow(cc), " = ", fshow(r), " ('b%b)", pack(e), ", expected ", fshow(rr), " ('b%b)", pack(ee));
	    cntErrors.up;
	 end
      end
      else begin
	 if (aa matches tagged Valid .aa_) begin
	    $display(fshow(aa_), " + ", fshow(bb), " * ", fshow(cc), " = ", fshow(r), " ('b%b)", pack(e));
	 end
	 else begin
	    $display("zero + ", fshow(bb), " * ", fshow(cc), " = ", fshow(r), " ('b%b)", pack(e));
	 end
      end
   endrule

   mkAutoFSM(test);

endmodule

endpackage
