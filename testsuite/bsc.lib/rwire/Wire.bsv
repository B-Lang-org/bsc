(* synthesize *)
module sysWire();
  Reg#(int) r <- mkReg(0);
  Wire#(int) w <- mkWire();

  rule send;
    w <= r;
  endrule: send

  rule receive;
    r <= w + 1;
  endrule: receive

  rule watch;
    $display("r = %d", r);
  endrule: watch

  rule stop(r == 10);
    $finish(0);
  endrule: stop
endmodule
