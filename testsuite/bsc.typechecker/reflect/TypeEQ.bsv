(* synthesize *)
module sysTypeEQ();

   rule test;
      $display(typeOf(True) == typeOf(1));
      $display(typeOf(noClock) == typeOf(clockOf(True)));
      $display(typeOf(Just(True)) == typeOf(Nothing));
      $finish(0);
   endrule

endmodule
