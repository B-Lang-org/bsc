(* synthesize *)
module mkBigRangeUpdate();

  Reg#(Bit#(65536)) x <- mkRegU;
  Reg#(Bit#(16384)) y <- mkRegU;

  rule test;
    x[32768:16385] <= y; 
  endrule

endmodule
