// Test dynamic selection of integers into bit buckets
// Should fail with out-of-range error

Integer one = 1;
Integer two = 2;

(* synthesize *)
module sysDynamicIntegerFail(Empty);
  Reg#(Bool) r <- mkReg(False);

  Bit#(1) x = fromInteger( r ? one : two);
  
  rule test;
    $display("x: %0d", x);
    $finish(0);
  endrule
endmodule
