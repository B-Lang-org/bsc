import FixedPoint::*;

interface CheckIfc#(type t);
   method Action check(t x);
endinterface

module mkCheck(CheckIfc#(FixedPoint#(i,f)))
   provisos (Add#(i,f,sz),                // sz = i+f
             Add#(1,sz_minus_1,sz),       // sz_minus_1 = sz - 1
             Bits#(FixedPoint#(1,sz_minus_1), TAdd#(i,f))
            );
   
   method Action check(FixedPoint#(i,f) x);
      Bit#(sz) bs = pack(x);
      FixedPoint#(1,sz_minus_1) tmp = unpack(bs);
   endmethod
   
endmodule

(* synthesize *)
module sysTypeTest2();
   
   CheckIfc#(FixedPoint#(3,14)) checker <- mkCheck();
   
   Reg#(FixedPoint#(3,14)) x <- mkRegU();
   
   rule r;
      checker.check(x);
   endrule
   
endmodule