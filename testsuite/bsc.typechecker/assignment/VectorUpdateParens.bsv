import Vector::*;

module sysTest(Empty);
   Reg#(Vector#(8,Vector#(8,Bool))) xss();
   mkRegU xss_r(xss);

   rule r (True);
      (xss[0][0]) <= True;
   endrule
endmodule
