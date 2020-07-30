(* synthesize *)
module sysBitInBounds2();
   Bit#(4) x = 4'b0101;
   Bit#(2) ix = -1;
   Bit#(1) y = x[ix];
   
   rule test;
      $display("%0b", y);
      $finish(0);
   endrule
   
endmodule
