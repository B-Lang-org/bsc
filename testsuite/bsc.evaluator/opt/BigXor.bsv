(* synthesize *)
module mkBigXor();

  Reg#(Bit#(65536)) x <- mkRegU;

  Bit#(16384) mask_base = '1;
  Bit#(65536) mask = {0, mask_base} << 16384;

  rule test;
    x <= x ^ mask;
  endrule

endmodule