import Vector::*;

module test(Vector#(n,Reg#(Bit#(32))));
   
   Vector#(n, Reg#(Bit#(32))) regs <- replicateM(mkReg(0));
   
   rule test;
      regs[5] <= True;
   endrule
   
   return regs;

endmodule


