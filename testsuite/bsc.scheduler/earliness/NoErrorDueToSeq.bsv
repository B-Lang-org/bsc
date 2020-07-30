// Test that no error is reported if the earliness is required, not due to
// an immediate edge in the graph, but due to a sequence of edges through
// other rules

(* synthesize *)
module mkNoErrorDueToSeq();
  Reg#(int) r <- mkReg(0);

  Reg#(int) rg1 <- mkReg(0);
  Reg#(int) rg2 <- mkReg(0);
  Reg#(int) rg3 <- mkReg(0);

  rule ambiguity_one;
    r <= 42;
    rg1 <= rg2;
  endrule
   
  rule mid;
    rg2 <= rg3;
  endrule

  rule ambiguity_two;
    r <= 24;
    rg3 <= 17;
  endrule
endmodule
