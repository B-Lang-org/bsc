import Vector::*;

interface Regs#(numeric type n);
   interface Vector#(n, Reg#(Bool)) vec;
endinterface

module mkRegs(Regs#(n))
   provisos(  Add#(_j1, 1, n), Log#(_j1, ln) );
endmodule

module sysLogZero(Regs#(1));
   let _m <- mkRegs;
   return _m;
endmodule

