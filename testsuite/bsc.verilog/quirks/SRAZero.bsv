(* synthesize *)
module mkSRAZero();

  Reg#(Int#(5)) r <- mkReg(0);

  Reg#(Int#(5)) s <- mkRegU;

  rule test;
    s <= r >> 0;
  endrule

endmodule
