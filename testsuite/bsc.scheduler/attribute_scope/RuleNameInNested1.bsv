(* synthesize *)
module sysRuleNameInNested1 ();

   Reg#(Bool) c1 <- mkRegU;
   Reg#(Bool) c2 <- mkRegU;

   rule common (c1);

      (* preempts = "branch1, branch2" *)
      rule branch1 (c2);
         $display("RL_common_branch1");
      endrule

      rule branch2;  // (!c2);
         $display("RL_common_branch2");
      endrule

   endrule: common

endmodule

