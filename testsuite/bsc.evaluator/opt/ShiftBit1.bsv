(* synthesize *)
module mkShiftBit1();

  Reg#(Bit#(1)) x <- mkRegU;
  Reg#(Bit#(15)) y <- mkRegU;

  Reg#(Bit#(1)) sl  <- mkRegU;
  Reg#(Bit#(1)) srl <- mkRegU;
  Reg#(Bit#(1)) sra <- mkRegU;

  rule test;
    sl <= x << y;
    srl <= x >> y;
    sra <= signedShiftRight(x,y);
  endrule

endmodule
