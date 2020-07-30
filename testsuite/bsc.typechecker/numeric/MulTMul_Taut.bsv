interface X#(numeric type x, numeric type y);
   method Action data(Bit#(TMul#(x, y)) d);
endinterface

module mkFoo
   // interface:
   (X#(x, y))
   provisos (Mul#(x, y, p));

   Reg#(Bit#(p)) s<- mkRegU();

   method Action data(Bit#(TMul#(x, y)) d);
       s<= d;
   endmethod
endmodule

