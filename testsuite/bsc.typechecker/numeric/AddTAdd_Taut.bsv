
interface X#(numeric type x, numeric type y);
   method Bit#(TAdd#(x, y)) getData();
endinterface

module mkFoo (X#(x, y));
   Reg#(Bit#(x)) rx <- mkRegU;
   Reg#(Bit#(y)) ry <- mkRegU;

   method Bit#(TAdd#(x, y)) getData();
       return {rx, ry};
   endmethod
endmodule

