(* synthesize *)
module sysDynamicDiv(Empty);

  Reg#(Bool) sel1 <- mkReg(False);
  Reg#(Bool) sel2 <- mkReg(False);

  Integer a = sel1 ? 24 : 12;
  Integer b = sel2 ? 2 : 3;

  rule flip;
    sel1 <= !sel1;
    if (sel1) sel2 <= !sel2;
  endrule

  rule test;
    $display ("Division result: %0d", a / b);
    if (sel1 && sel2) $finish(0);
  endrule

endmodule

