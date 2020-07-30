import Vector::*;

(* synthesize *)
module sysPulseTest(Empty);

  Reg#(Bool) a <- mkReg(False);
  PulseWire b <- mkPulseWire;

  Vector#(2, Bool) x = replicate(?);
  x[0] = a;
  x[1] = b;

  rule pulse(!a);
    b.send;
  endrule

  rule test;    
    $display("a: %0b b: %0b", x[0], x[1]);
    $finish(0);
  endrule

endmodule
 
