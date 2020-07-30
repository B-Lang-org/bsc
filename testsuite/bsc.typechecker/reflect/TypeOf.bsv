(* synthesize *)
module sysTypeOf();

   rule test;
      $write(printType(typeOf(1)));
      $finish(0);
   endrule

endmodule
