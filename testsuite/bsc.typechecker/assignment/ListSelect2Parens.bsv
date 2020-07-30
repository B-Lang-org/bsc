import List::*;

module sysTest(Empty);
   List#(List#(Reg#(Bool))) xss;
   xss <- mapM( constFn(mapM(constFn(mkReg(False)),upto(0,7))), upto(0,7)) ;

   rule r (True);
      (xss[0][0]) <= True;
   endrule
endmodule
