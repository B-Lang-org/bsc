(* synthesize *)
module mkDisjointTest(Empty);

   Reg#(Bit#(8)) a <- mkReg(0);
   Reg#(Bit#(8)) b <- mkReg(0);
   Reg#(Bit#(8)) c <- mkReg(0);
   
   rule one(a == 0);
      b <= 1;
   endrule
   
   rule two(a == 1);
      b <= 2;
   endrule
   
   rule three(a == 2);
      c <= 3;
   endrule
   
endmodule
