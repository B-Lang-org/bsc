// Test that an if-expr inside an if-expr is sufficient to create a case-expr

(* synthesize *)
module sysSmallCase();
   Reg#(int) rg <- mkReg(0);

   rule r;
      int v;
      if (rg == 0)
	 v = 1;
      else if (rg == 1)
	 v = 2;
      else
	 v = 3;
      rg <= v;
   endrule

endmodule

