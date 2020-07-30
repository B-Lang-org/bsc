(* synthesize *)
module sysERulesMux2a_ArrSel(Reg#(Bool));

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

   module#(Empty) ms[4];
   ms[0] = addRules(r1);
   ms[1] = addRules(r2);
   ms[2] = addRules(r3);
   ms[3] = addRules(emptyRules);

   ms[idx];

   method _read = ?;
   method _write(x) = ?;
endmodule
