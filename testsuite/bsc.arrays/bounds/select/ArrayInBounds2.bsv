(* synthesize *)
module sysArrayInBounds2();
   Integer x[4] = {1, 2, 3, 4};
   Bit#(2) ix = -1;
   Integer y = x[ix];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule
