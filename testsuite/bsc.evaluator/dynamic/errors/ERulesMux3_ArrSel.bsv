(* synthesize *)
module sysERulesMux3_ArrSel();

   Reg#(Bit#(2)) idx <- mkReg(0);

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);
   Reg#(Bool) c3 <- mkReg(True);

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
   Rules r3 = rules
		 rule do3 (c3);
		    $display("r3");
		 endrule
	      endrules;

   Rules rs[4];
   rs[0] = r1;
   rs[1] = r2;
   rs[2] = r3;
   rs[3] = emptyRules;

   addRules(rs[idx]);

endmodule
