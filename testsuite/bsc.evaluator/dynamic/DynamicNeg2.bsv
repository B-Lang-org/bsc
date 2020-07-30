(* synthesize *)
module sysDynamicNeg2(Empty);

  Reg#(Bool) b <- mkReg(False);
  Reg#(Bit#(2)) c <- mkReg(0);

  Integer i = b ? -5 : 7;
  Integer j = (c[1] == 1) ? 12 : -3;

  rule test;
    b <= !b;
    c <= c + 1;
    $display("-(i+j): %0d", -(i+j));
    if (c == 3) $finish(0);
  endrule

endmodule
