(* synthesize *)
module sysUndetIf ();
   Reg#(Bool) p1 <- mkRegU;
   Reg#(Bool) p2 <- mkRegU;

   Reg#(int) d <- mkRegU;
   Reg#(int) i <- mkRegU;

   rule update;
      int v;
      if (p1)
	 v = ?;
      else
	 if (p2)
	    v = d;
	 else
	    v = i;
      d <= v;
   endrule

endmodule
