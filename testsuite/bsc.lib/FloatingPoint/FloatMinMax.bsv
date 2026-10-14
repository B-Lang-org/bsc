import FloatingPoint::*;
import StmtFSM::*;

(* synthesize *)
module sysFloatMinMax(Empty);
   Reg#(Float) x <- mkReg(unpack(0));
   Reg#(Float) y <- mkReg(unpack(0));

   function Stmt test(Bit#(32) a, Bit#(32) b);
      return seq
         action
            x <= unpack(a);
            y <= unpack(b);
         endaction
         $display("x=%h y=%h min=%h max=%h", pack(x), pack(y),
                  pack(min(x, y)), pack(max(x, y)));
      endseq;
   endfunction

   mkAutoFSM(seq
      test(32'hbf800000, 32'hc0800000); // negative, different exponents
      test(32'hc0800000, 32'hbf800000); // swapped
      test(32'hbfc00000, 32'hbfa00000); // negative, equal exponents
      test(32'hbfa00000, 32'hbfc00000); // swapped
      test(32'h3f800000, 32'h40800000); // positive
      test(32'h40800000, 32'h3f800000); // swapped
      test(32'h3fc00000, 32'h3fa00000); // positive, equal exponents
      test(32'hbf800000, 32'h3f800000); // opposite signs
      test(32'h3f800000, 32'hbf800000); // swapped
      test(32'hbf800000, 32'hbf800000); // equal negative values
      test(32'h80000000, 32'h00000000); // signed zeros
      test(32'h00000000, 32'h80000000); // swapped
      test(32'hff800000, 32'hbf800000); // negative infinity
      test(32'hbf800000, 32'hff800000); // swapped
      test(32'h80000001, 32'h80000002); // negative subnormals
      test(32'h80000002, 32'h80000001); // swapped
      test(32'h00000000, 32'h00000000); // equal positive zeros
      test(32'h80000000, 32'h80000000); // equal negative zeros
      test(32'h7fc00001, 32'hbf800000); // quiet NaN
      test(32'hbf800000, 32'h7fc00001); // swapped
      test(32'h7f800001, 32'hbf800000); // signaling NaN
      test(32'hbf800000, 32'h7f800001); // swapped
      test(32'h7fc00001, 32'h7fc00002); // quiet NaN priority
      test(32'h7fc00001, 32'h7f800002); // signaling NaN priority
   endseq);
endmodule
