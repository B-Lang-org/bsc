(* synthesize *)
module sysPropDeduce_SubmodUseInhigh ();
   mkPropDeduce_SubmodUseInhigh_Sub;
endmodule

// We need a submodule which cares about its gate
(* synthesize *)
module mkPropDeduce_SubmodUseInhigh_Sub ();
   Reg#(Bool) rg <- mkReg(True);
   rule r;
      $display("rg = ", rg);
      rg <= !rg;
   endrule
endmodule

