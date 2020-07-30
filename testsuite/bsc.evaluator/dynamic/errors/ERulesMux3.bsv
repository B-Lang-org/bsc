(* synthesize *)
module sysERulesMux3();

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

   addRules( b ? r1 : r2 );

endmodule
