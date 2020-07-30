(* synthesize *)
module sysERulesMux2a(Reg#(Bool));

   Reg#(Bool) b <- mkReg(True);

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   Rules r1 = rules
		 rule do1 (c1);
		    $display("r1");
		 endrule
	      endrules;
   Rules r2 = rules
		 rule do2 (c2);
		    $display("r2");
		 endrule
	      endrules;
   
   if (b)
      addRules(r1);
   else
      addRules(r2);

   method _read = ?;
   method _write(x) = ?;
endmodule
