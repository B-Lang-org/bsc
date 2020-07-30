typedef Int#(17) T;

(* synthesize*)
module sysMergeIf2 ();
   Reg#(T) w <- mkReg(0);
   Reg#(T) x <- mkReg(0);
   Reg#(T) y <- mkReg(5);
   Reg#(T) z <- mkReg(5);

   Reg#(Bool) c1 <- mkReg(False);
   Reg#(Bool) c2 <- mkReg(False);
   Reg#(Bool) c3 <- mkReg(False);
   Reg#(Bool) c4 <- mkReg(False);
   
   rule r;
      if (c1 && c2)
         w <= 0;
      // False branch
      if (c3 && !c2 && !c1)
         x <= 1;
      // True branch
      // (keep this branch a single action, to test that no subbranch is made)
      if (c2 && c3 && c4 && c1)
         y <= 2;
      // False branch, then True subbranch
      // (tests that a subbranch is created, and leave an empty False branch)
      if (c4 && !c1 && c3 && !c2)
         z <= 3;
   endrule
   
endmodule
