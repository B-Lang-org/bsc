(* synthesize *)
module mkWarnFalse();

  Reg#(Bool) b <- mkReg(True);
  Reg#(UInt#(21)) r <- mkReg(17);

  rule test(b && !b);
    r <= 42;
  endrule

endmodule
