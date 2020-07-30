(* synthesize *)
module sysUndetRules2();
   Reg#(int) rg <- mkReg(0);
   Rules ruleSet = ?;
   for (Integer i = 0; i < 3; i = i + 1) begin
      Rules r = rules
                  rule r;
                     rg <= rg + fromInteger(i);
                  endrule
                endrules;
      ruleSet = rJoinPreempts(r, ruleSet);
   end

   addRules(ruleSet);
endmodule

