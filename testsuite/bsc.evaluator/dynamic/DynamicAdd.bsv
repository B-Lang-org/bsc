(* synthesize *)
module sysDynamicAdd(Empty);

  Reg#(Bit#(3)) c <- mkReg(0);

  Integer i = (c[0] == 1) ? -5 : 7;
  Integer j = (c[1] == 1) ? 12 : -3;
  Integer k = (c[2] == 1) ? 7 : -4;

  rule test;
    c <= c + 1;
    $display("i+j+k: %0d", (i+j)+k);
    if (c == 7) $finish(0);
  endrule

endmodule
