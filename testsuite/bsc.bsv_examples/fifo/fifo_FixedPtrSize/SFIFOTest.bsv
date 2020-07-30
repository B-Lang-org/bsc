import SFIFOSupport::*;

module mkSFIFOTest(Empty);

  Reg#(Bool) b();
  mkReg#(False) the_b(b);

  Reg#(Bit#(8)) r();
  mkReg#(0) the_r(r);

  SFIFO#(Bit#(4)) f();
  mkSFIFO the_f(f);

  rule r1 (!b && !f.isFull);
    Bit#(4) val = truncate(r);
    $display("Enqueuing: %0d", val);
    f.enq(val);
    r <= r + 1;
  endrule

  rule r2 (!b && f.isFull);
    $display("FIFO is full");
    b <= True;
  endrule

  rule r3 (b && !f.isEmpty);
    $display("Dequeuing: %0d", f.first());
    f.deq();
  endrule

  rule r4 (b && f.isEmpty);
    $display("Done");
    $finish(0);
  endrule

endmodule

