(* synthesize *)
module mkFoo ();

   Reg#(Bit#(2048)) foo <- mkRegU;
   Reg#(bit)       foo2 <- mkRegU;

   rule doit;
      (foo[0]) <= foo2; // parens don't make a difference
   endrule

endmodule
