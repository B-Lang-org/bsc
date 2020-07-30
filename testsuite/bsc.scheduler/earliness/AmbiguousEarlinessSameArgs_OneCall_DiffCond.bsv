(* synthesize *)
module mkAmbiguousEarlinessSameArgs_OneCall_DiffCond ();
   Reg#(Bit#(8)) rg <- mkReg(0);

   Reg#(Bool) cond1 <- mkReg(True);
   Reg#(Bool) cond2 <- mkReg(False);

   rule rl_A (cond1);
      rg <= 0;
   endrule

   rule rl_B (cond2);
      rg <= 0;
   endrule
endmodule

