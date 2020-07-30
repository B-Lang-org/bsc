Integer x0 = 1;
Integer y0 = 15;
Int#(5) x = fromInteger(x0);
Int#(5) y = fromInteger(y0);

(* synthesize *)
module sysPositiveIntOK();

   rule test;
      $display("x: %0d y: %0d", x, y);
      $finish(0);
   endrule

endmodule
