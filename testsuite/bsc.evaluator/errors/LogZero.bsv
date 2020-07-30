(* synthesize *)
module sysLogZero();
   rule test;
      Integer x = 0;
      $display(log2(x));
      $finish(0);
   endrule
endmodule
