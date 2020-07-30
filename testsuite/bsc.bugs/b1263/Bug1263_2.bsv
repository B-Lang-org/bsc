typedef Reg#(a) R#(type a);

module mkR(R#(a)) provisos(Bits#(a, sa));
  let r <- mkRegU;
  return(r);
endmodule

module test();

  R b <- mkR;

  rule r (b);
     $display("hi");
  endrule

endmodule
