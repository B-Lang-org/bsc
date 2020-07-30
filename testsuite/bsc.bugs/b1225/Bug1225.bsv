import Vector::*;

interface Rotate#(numeric type n, type a_T);
   method Vector#(n, a_T) value();
   method Action rotate(Nat start);
endinterface

module mkRotate#(Vector#(n, a_T) init)(Rotate#(n, a_T)) provisos(Bits#(a_T, pa_T));
 
function Vector#(n, a_T) rotateBitVector(Vector#(n, a_T) xs, Nat start);
     Bit#(vsz) pxs = pack(xs);
     Nat s     = fromInteger(valueof(pa_T));
     Nat shVal = start * s;
     let size =  fromInteger(valueof(SizeOf#(Vector#(n, a_T))));
     let bottom =  pxs << start;
     let top =  pxs >> size - start;
     return (unpack(top | bottom));
endfunction

   Reg#(Vector#(n, a_T)) r <- mkReg(init);

   method value = r;
   method Action rotate(Nat start);
      r <= rotateBitVector(r, start);
   endmethod

endmodule
