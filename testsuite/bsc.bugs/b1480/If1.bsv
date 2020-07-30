(* synthesize *)
module sysIf1();
   
   Reg#(UInt#(4)) idx <- mkReg(0);
   Reg#(Bit#(64)) x   <- mkReg(0);
   Reg#(Bit#(64)) y   <- mkReg(0);
   
   rule incr;
      idx <= idx + 1;
   endrule
   
   rule work;
      if (idx < 4)
      begin
	if (x[idx] == 1)
	   x <= y + 1;
      end
      else
      begin
	 y <= ~y;
         x <= x + 1;
      end
   endrule
   
   rule done (idx == 15);
      $finish(0);
   endrule
   
endmodule