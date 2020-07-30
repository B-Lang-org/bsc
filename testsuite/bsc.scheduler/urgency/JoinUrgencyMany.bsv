// Test that rJoinDescendingUrgency applied to two groups of rules
// doesn't create relationships between rules in the same group

(* synthesize *)
module sysJoinUrgencyMany ();
   Reg#(Bool) b1 <- mkReg(True);
   Reg#(Bool) b2 <- mkReg(True);
   Reg#(Bool) b3 <- mkReg(True);

   Reg#(int) rg <- mkReg(0);

   Rules rs1 = rules
		  rule r1 (b1);
		     rg <= rg + 1;
		  endrule

		  rule r2 (b2);
		     rg <= rg + 2;
		  endrule
	       endrules;

   Rules rs2 = rules
		  rule r3 (b3);
		     rg <= rg + 3;
		  endrule
	       endrules;

   // there should still be an arbitrary urgency choice between r1 and r2
   addRules( rJoinDescendingUrgency(rs1,rs2) );
endmodule

