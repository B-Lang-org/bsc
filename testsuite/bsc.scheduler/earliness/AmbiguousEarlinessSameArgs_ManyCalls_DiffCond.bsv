(* synthesize *)
module mkAmbiguousEarlinessSameArgs_ManyCalls ();
   Reg#(Bit#(8)) rg <- mkReg(0);

   Reg#(Bool) cond1 <- mkReg(True);
   Reg#(Bool) cond2 <- mkReg(False);

   rule rl_A;
      if (cond1)
         rg <= 0;
      else if (cond2)
         rg <= 1;
      else
         rg <= 2;
   endrule

   rule rl_B;
      if (cond2)
         rg <= 0;
      else if (cond1)
         rg <= 1;
      else
         rg <= 2;
   endrule
endmodule

