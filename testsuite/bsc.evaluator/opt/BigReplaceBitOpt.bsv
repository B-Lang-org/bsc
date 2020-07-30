(* synthesize *)
module mkBigReplaceBitOpt();

  Reg#(Bit#(65536)) r <- mkRegU;
  Reg#(Bit#(1)) s <- mkRegU;

  rule test;
    Bit#(65536) r_new = r;
    for(Integer i = 1; i < 65536; i = i * 2)
    begin
      r_new[i] = s;
    end
    r <= r_new;
  endrule

endmodule

