(* synthesize *)
module mkBigXor2();

  Reg#(Bit#(65536)) x <- mkRegU;

  Bit#(65536) mask0 = 65536'haaaaaaaa;
  Bit#(65536) mask = mask0;

  for(Integer i = 1; i < 32; i = i + 1)
  begin
    mask = message(integerToString(i), (mask << 32) | mask0);
  end

  rule test;
    x <= x ^ mask;
  endrule

endmodule