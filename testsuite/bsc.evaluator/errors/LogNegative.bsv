(* synthesize *)
module sysLogNegative();
   rule test;
      Integer x = -1;
      $display(log2(x));
      $finish(0);
   endrule
endmodule
