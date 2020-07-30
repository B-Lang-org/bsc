import List::*;

module sysTest(Empty);
   List#(Reg#(Bool)) xs;
   xs <- mapM(constFn(mkReg(False)),upto(0,7));

   rule r (True);
      xs <= True;
   endrule
endmodule
