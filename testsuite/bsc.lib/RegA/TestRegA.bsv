(* synthesize *)
module sysTestRegA(Empty);

  Reg#(Bit#(23)) r <- mkRegA(17);

  Reg#(Bool) started <- mkRegA(False);

  rule start(!started);
    started <= True;
    $display("r: %0d", r);
    r <= r + 1;
  endrule

  rule exit(started);
    $display("r: %0d", r);
    $finish(0);
  endrule

endmodule
