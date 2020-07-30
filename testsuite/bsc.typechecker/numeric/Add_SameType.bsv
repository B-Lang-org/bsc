import Vector::*;

typedef TAdd#(x,x) TDouble#(numeric type x);

typedef Bit#(TDouble#(o)) Value#(numeric type o);

typedef Vector#(n,Vector#(m,t)) Grid#(numeric type n, numeric type m, type t);

typedef Grid#(o,o,Reg#(Value#(o))) RegGrid#(numeric type o);

function Value#(o) allOnes();
  return unpack('1);
endfunction

module sysAdd_SameType();

  RegGrid#(3) grid <- replicateM(replicateM(mkReg(allOnes())));

endmodule

