(* synthesize *)
module mkAmbiguousEarlinessSameArgs_OneCall ();
   Reg#(Bit#(8)) rg <- mkReg(0);

   rule rl_A;
      rg <= 0;
   endrule

   rule rl_B;
      rg <= 0;
   endrule
endmodule

