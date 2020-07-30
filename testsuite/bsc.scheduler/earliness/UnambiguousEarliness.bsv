(* synthesize *)
module mkUnambiguousEarliness();
  Reg#(int) r <- mkReg(0);
  rule unambiguity_one;
    r <= 42;
  endrule
  rule unambiguity_two;
    r <= r+1;
  endrule
endmodule
