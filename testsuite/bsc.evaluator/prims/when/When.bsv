(* synthesize *)
module sysWhen(Empty);

  Reg#(Bit#(6)) r <- mkReg(0);

  rule test;
    when(r[0] == 0, $display("r is %0d", r));
  endrule

  rule inc;
    r <= r + 1;
  endrule

  rule exit(r == 11);
    $finish(0);
  endrule

endmodule

