(* synthesize *)
module mkMutuallyExclusiveOK(Empty);

   Reg#(Bit#(64)) r <- mkReg(0);
   
   rule zero(r == 0);
      r <= 1;
   endrule
   
   (* mutually_exclusive = "zero, one" *)
   rule one(r == 1);
      r <= 0;
   endrule
   
endmodule

