import Vector::*;

module test(Vector#(n,Reg#(Bit#(32))));
   
   Vector#(n, Reg#(Bit#(32))) regs <- replicateM(mkReg(0));
   
   Integer i = 5;
   
   rule test;
      regs[i] <= True;
   endrule
   
   return regs;

endmodule


