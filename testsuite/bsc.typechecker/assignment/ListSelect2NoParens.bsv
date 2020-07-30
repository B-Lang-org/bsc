import List::*;

module sysTest(Empty);
   List#(List#(Reg#(Bool))) xss;
   xss <- replicateM(8, replicateM(8, mkReg(False)));

   rule r (True);
      xss[0][0] <= True;
   endrule
endmodule
