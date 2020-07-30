(* synthesize *)
module mkReplaceBitOpt();

  Reg#(Bit#(2048)) r <- mkRegU;
  Reg#(Bit#(1)) s <- mkRegU;

  rule test;
    r[1024] <= s;
  endrule

endmodule

