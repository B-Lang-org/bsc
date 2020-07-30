(* synthesize *)
module mkDisjointTest(Empty);

   Reg#(Bit#(8)) a <- mkReg(0);
   Reg#(Bit#(8)) b <- mkReg(0);
   Reg#(Bit#(8)) c <- mkReg(0);
   Reg#(Bit#(8)) d <- mkReg(0);
   
   rule one(a == 0);
      b <= 1;
   endrule
   
   rule two(a == 1);
      b <= 2;
   endrule
   
   rule three(a == 2);
      c <= 3;
   endrule
   
   rule four(d == 0);
      d <= 4;
   endrule

   rule five;
      d <= d - 1;
   endrule
   
endmodule
