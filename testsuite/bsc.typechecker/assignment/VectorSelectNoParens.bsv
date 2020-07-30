import Vector::*;

module sysTest(Empty);
   Vector#(8,Reg#(Bool)) xs;
   xs <- mapM(constFn(mkReg(False)),genList);

   rule r (True);
      xs[0] <= True;
   endrule
endmodule
