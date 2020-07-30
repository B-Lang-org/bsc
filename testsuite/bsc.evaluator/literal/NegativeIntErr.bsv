Integer x0 = -1;
Integer y0 = -17;
Int#(5) x = fromInteger(x0);
Int#(5) y = fromInteger(y0);

(* synthesize *)
module sysNegativeIntErr();

   rule test;
      $display("x: %0d y: %0d", x, y);
      $finish(0);
   endrule

endmodule
