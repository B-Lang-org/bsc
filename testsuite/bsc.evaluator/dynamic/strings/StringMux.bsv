(* synthesize *)
module sysStringMux();

  Reg#(Bool) b <- mkReg(False);

  String x = b ? "b is True" : "b is False";

  rule test;
    $display(x);
    $display("Length is %0d", stringLength(x));
    b <= !b;
    if(b) $finish(0);
  endrule

endmodule
