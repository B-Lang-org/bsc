(* synthesize *)
module sysTypeOf();

   rule test;
      // Use $display (with trailing newline) rather than $write: a newline-less
      // $write puts verilator's "$finish" banner on the same line, which the
      // output filter then strips along with the value.  The newline keeps them
      // on separate lines so all simulators agree.  (This test checks type
      // reflection, so the trailing newline is immaterial to what it exercises.)
      $display(printType(typeOf(1)));
      $finish(0);
   endrule

endmodule
