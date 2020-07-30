// test if cond a b ++ if cond c d -> if cond (a ++ c) (b ++ d) 
interface Test;
  method Bit#(7) out;
endinterface

(* synthesize *)
module sysITransformConcatIf(Test);

  Reg#(Bool) cond <- mkRegU;
  Reg#(Bit#(3)) a <- mkRegU;
  Reg#(Bit#(3)) b <- mkRegU;
  Reg#(Bit#(4)) c <- mkRegU;
  Reg#(Bit#(4)) d <- mkRegU;

  method out = { cond ? a : b, cond ? c : d };

endmodule
