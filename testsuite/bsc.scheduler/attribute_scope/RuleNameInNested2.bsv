(* synthesize *)
module sysRuleNameInNested ();

   Reg#(Bool) c1 <- mkRegU;
   Reg#(Bool) c2 <- mkRegU;

   Reg#(UInt#(16)) rg <- mkRegU;

   // Note that, without a non-rule between them, these are in the same
   // implicit rules block.  Consider also testing when they are separate.
   //
   rule r1;
      rg <= rg + 1;
   endrule

   rule common (c1);

      (* descending_urgency="branch1, r1" *)
      rule branch1 (c2);
         $display("RL_common_branch1");
	 rg <= rg + 2;
      endrule

      rule branch2;  // (!c2);
         $display("RL_common_branch2");
      endrule

   endrule: common

endmodule
