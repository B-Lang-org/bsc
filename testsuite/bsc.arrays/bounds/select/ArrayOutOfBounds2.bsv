(* synthesize *)
module sysArrayOutOfBounds2();
   Integer x[4] = {1, 2, 3, 4};
   Integer y = x[-1];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
