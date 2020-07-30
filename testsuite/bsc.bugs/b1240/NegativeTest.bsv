import Vector::*;

typedef 5 A;
typedef 6 B;
typedef TSub#(A, B) C;

interface Foo#(numeric type n);
   interface Vector#(n, Reg#(Bit#(8))) regs;
endinterface
      
(* synthesize *)
module mkTest(Foo#(C));
   interface regs = replicate(mkReg(0));
endmodule

