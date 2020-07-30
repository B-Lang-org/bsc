(* synthesize *)
module sysPropDeduce_RuleUse ();
   Reg#(Bool) rg <- mkReg(True);
   rule r;
      $display("rg = ", rg);
      rg <= !rg;
   endrule
endmodule
