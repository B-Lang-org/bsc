import Complex::*;
import FShow::*;
import DefaultValue::*;

// Test of Complex Saturating and FShow

(*synthesize*)
module sysCmplxSatAdd();
   Reg#(Complex#(Int#(10)))  c1 <- mkReg(defaultValue);
   Reg#(Complex#(Int#(10)))  c2 <- mkReg(200);
   Reg#(Complex#(Int#(10)))  c3 <- mkReg(3);
   Reg#(Int#(10))     cnt <- mkReg(0);
   
   rule tester (True);
   // $display ("%d: ", cnt, fshow(c1), " " , fshow(c2), " ", fshow(c3));
      $display ("%0d: <%0d, %0d> <%0d, %0d> <%0d, %0d>", cnt, c1.rel, c1.img, c2.rel, c2.img, c3.rel, c3.img);
      c1 <= boundedPlus  (c1, c3);
      c2 <= boundedMinus (c2, c3);
      c3 <= cmplxSwap(c3) * -2 + 1;
      cnt <= cnt + 1;
      if (cnt > 16) $finish(0);
   endrule
endmodule
