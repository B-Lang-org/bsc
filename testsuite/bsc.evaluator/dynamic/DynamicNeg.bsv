(* synthesize *)
module sysDynamicNeg(Empty);

  Reg#(Bool) b <- mkReg(False);

  Integer i = b ? -5 : 7;

  rule flip;
     b <= !b;
  endrule

  rule test;
    $display("i: %0d", -i);
    if (b) $finish(0);
  endrule

endmodule
