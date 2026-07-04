(* synthesize *)
module sysTypeOf();

   rule test;
      $display(printType(typeOf(1)));
      $finish(0);
   endrule

endmodule
