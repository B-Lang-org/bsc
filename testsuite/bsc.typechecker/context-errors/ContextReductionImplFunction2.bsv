import Vector::*;

module sysContextReductionImplFunction (Empty);

   Vector#(4, Reg#(Bit#(2))) p <- replicateM(mkReg(0));
   Reg#(Bit#(8)) x <- mkReg(0);

   function test (a);
      action
	 if (p[0]) 
            x <= a;
	 else 
            x <= ~a;
      endaction
   endfunction

   rule r (True);
      test(x);
   endrule

endmodule
