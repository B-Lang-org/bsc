(* synthesize *)
module sysBitInBounds2();
   Bit#(4) x = 0;
   Bit#(2) ix = -1;
   x[ix] = 1;
   
   rule test;
      $display("%b", x);
      $finish(0);
   endrule
   
endmodule
