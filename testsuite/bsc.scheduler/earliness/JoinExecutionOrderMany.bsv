// Test rJoinExecutionOrder specifies relationships between two groups
// but does not create relationships between rules in the same group

(* synthesize *)
module sysJoinExecutionOrderMany ();
   Reg#(Bool) b1 <- mkReg(True);
   Reg#(Bool) b2 <- mkReg(True);
   Reg#(Bool) b3 <- mkReg(True);

   Reg#(int) rg <- mkReg(0);

   Rules rs1 = rules
		  rule r1 (b1);
		     rg <= 1;
		  endrule

		  rule r2 (b2);
		     rg <= 2;
		  endrule
	       endrules;

   Rules rs2 = rules
		  rule r3 (b3);
		     rg <= 3;
		  endrule
	       endrules;

   // there should still be an arbitrary order choice between r1 and r2
   addRules( rJoinExecutionOrder(rs1,rs2) );
endmodule

