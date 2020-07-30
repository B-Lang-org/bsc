// Test dynamic selection of integers into bit buckets

Integer one = 1;
Integer two = 2;
Integer three = 3;
Integer four = 4;

module sysDynamicIntegerNested(Empty);
  Reg#(Bool) r <- mkReg(False);
  Reg#(Bool) s <- mkReg(False);

  Integer y1 = s ? one : two;
  Integer y2 = s ? three : four;

  Bit#(3) x = fromInteger( r ? y1 : y2);
                               
  rule test;
    $display("x: %0d", x);
    $finish(0);
  endrule

endmodule
