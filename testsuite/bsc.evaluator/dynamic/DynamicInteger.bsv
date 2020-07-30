// Test dynamic selection of integers into bit buckets

Integer one = 1;
Integer two = 2;

module sysDynamicInteger(Empty);
  Reg#(Bool) r <- mkReg(False);

  Bit#(2) x = fromInteger( r ? one : two);
  
  rule test;
    $display("x: %0d", x);
    $finish(0);
  endrule
endmodule
