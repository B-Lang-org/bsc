import Vector::*;

typedef TMul#(x,x) TSquare#(numeric type x);

typedef Bit#(TSquare#(o)) Value#(numeric type o);

typedef Vector#(n,Vector#(m,t)) Grid#(numeric type n, numeric type m, type t);

typedef Grid#(o,o,Reg#(Value#(o))) RegGrid#(numeric type o);

function Value#(o) allOnes();
  return unpack('1);
endfunction

module sysMul_SameType();

  RegGrid#(3) grid <- replicateM(replicateM(mkReg(allOnes())));

  // Workaround
  // Value#(3) = allOnes();
  // RegGrid#(3) grid <- replicateM(replicateM(mkReg(x)));

endmodule

