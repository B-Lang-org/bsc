(* synthesize *)
module mkAmbiguousEarliness();
  Reg#(int) r <- mkReg(0);
  rule ambiguity_one;
    r <= 42;
  endrule
  rule ambiguity_two;
    r <= 24;
  endrule
endmodule
