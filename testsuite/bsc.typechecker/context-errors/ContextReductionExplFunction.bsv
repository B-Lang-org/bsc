module sysContextReductionExplFunction (Empty);

   Reg#(Bit#(4)) p <- mkReg(0);
   Reg#(Bit#(8)) x <- mkReg(0);

   function Action test (Bit#(8) a);
      action
	 if (p[0]) 
            x <= a;
	 else 
            x <= ~a;
      endaction
   endfunction

endmodule
