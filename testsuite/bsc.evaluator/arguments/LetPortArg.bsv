(* synthesize *)
module mkPort#(Bit#(16) y)(Empty);

   let x = exp(2,8);
   rule test;
      $display("x: %0d", x);
      $display("x+y: %0d", fromInteger(x) + y);
      $finish(0);
   endrule

endmodule

