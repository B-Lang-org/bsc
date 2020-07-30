(* synthesize *)
module mkStringConcat1Sub#(parameter String a, parameter String b)();

  rule test;
    $display( a + ", " + b, 5'd27, 8'd254);
    $finish(0);
  endrule

endmodule

(* synthesize *)
module sysStringConcat1();

  Empty m <- mkStringConcat1Sub("First arg: %0b", "Second arg: %0h");

endmodule
