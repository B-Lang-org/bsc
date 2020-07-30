(* synthesize *)
module sysNegativeExp();
   rule test;
      $display(2 ** -1);
      $finish(0);
   endrule
endmodule
