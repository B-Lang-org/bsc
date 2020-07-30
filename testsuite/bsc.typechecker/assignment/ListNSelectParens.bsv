import ListN::*;

module sysTest(Empty);
   ListN#(8,Reg#(Bool)) xs;
   xs <- mapM(constFn(mkReg(False)),genList);

   rule r (True);
      (xs[0]) <= True;
   endrule
endmodule
