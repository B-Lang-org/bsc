interface TestIFC;
    method Action test (Bit#(8) a);
endinterface

module sysContextReductionMethod (TestIFC);

   Reg#(Bit#(4)) p <- mkReg(0);
   Reg#(Bit#(8)) x <- mkReg(0);

   method test (a);
      action
	 if (p[0]) 
            x <= a;
	 else 
            x <= ~a;
      endaction
   endmethod

endmodule
