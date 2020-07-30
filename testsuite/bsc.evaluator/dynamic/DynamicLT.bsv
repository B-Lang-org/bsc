(* synthesize *)
module sysDynamicLT(Empty);

  Reg#(Bool) sel1 <- mkReg(False);
  Reg#(Bool) sel2 <- mkReg(False);

  Integer a = sel1 ? 24 : 3;
  Integer b = sel2 ? 2 : 12;

  rule flip;
    sel1 <= !sel1;
    if (sel1) sel2 <= !sel2;
  endrule

  rule test;
    if (a < b)
      $display("%0d is less than %0d", a, b);
    else 
      $display("%0d is not less than %0d", a, b);
    if (sel1 && sel2) $finish(0);
  endrule

endmodule

