(* synthesize *)
module sysERulesMux2a_Case(Reg#(Bool));

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

   case (idx)
      0 : addRules(r1);
      1 : addRules(r2);
      2 : addRules(r3);
      default : addRules(emptyRules);
   endcase

   method _read = ?;
   method _write(x) = ?;
endmodule
