typedef Int#(17) T;

(* synthesize*)
module sysMergeIf3 ();
   Reg#(T) x <- mkReg(0);
   Reg#(T) y <- mkReg(5);
   Reg#(T) z <- mkReg(5);

   Reg#(Bool) c1 <- mkReg(False);
   Reg#(Bool) c2 <- mkReg(False);

   Reg#(Bool) c3 <- mkReg(False);
   Reg#(Bool) c4 <- mkReg(False);
   Reg#(Bool) c5 <- mkReg(False);
   
   rule r1;
      // test that we also merge when the following action is a subset
      if (c1) begin
         // this will be seen as an action with cond "c1 && c2"
         if (c2)
            x <= 0;
         // this action will have a subset condition, "c1"
         y <= 1;
      end
   endrule

   // set up a situation where we already merged into an "if"
   // where the subsequent action has a subset condition
   rule r2;
      if (c3) begin
         if (c4) begin
            if (c5)
               x <= 0;
            y <= 1;
         end
         z <= 2;
      end
   endrule
   
endmodule
