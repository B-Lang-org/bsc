// Validate that static selection if integers is not broken

Integer one = 1;
Integer two = 2;

module sysStaticInteger(Empty);

  Bit#(2) x = fromInteger( True ? one : two);
  
  rule test;
    $display("x: %0d", x);
    $finish(0);
  endrule

endmodule
