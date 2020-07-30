import Vector::*;

interface X#(numeric type x, numeric type y);
   method Action data(Bit#(TMul#(x, y)) d);
endinterface

module mkFoo (X#(x, y));
   Reg#(Vector#(x,Bit#(y))) s <- mkRegU;

   method Action data(Bit#(TMul#(x, y)) d);
       s <= unpack(d);
   endmethod
endmodule

