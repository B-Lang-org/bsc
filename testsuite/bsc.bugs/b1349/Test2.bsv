import FixedPoint::*;

// Move the fixed point of a value without changing the
// total number of bits.  This is like a shift that does not lose
// any precision, and it is purely a type-level operation with
// no hardware cost.
function FixedPoint#(ri,rf) movePoint(FixedPoint#(i,f) a)
   provisos(Bits#(FixedPoint#(ri,rf),TAdd#(i,f)));
   return unpack(pack(a));
endfunction: movePoint

interface CheckIfc#(type t);
   method Action check(t x);
endinterface

module mkCheck(CheckIfc#(FixedPoint#(i,f)))
   provisos (Bits#(FixedPoint#(f,i), TAdd#(i,f))); 
   
   method Action check(FixedPoint#(i,f) x);
      FixedPoint#(f,i) tmp = movePoint(x);
   endmethod
   
endmodule

(* synthesize *)
module sysTypeTest();
   
   let checker <- mkCheck();
   
   Reg#(FixedPoint#(3,14)) x <- mkRegU();
   
   rule r;
      checker.check(x);
   endrule
   
endmodule