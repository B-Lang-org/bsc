(* synthesize *)
module sysBitInBounds1();
   Bit#(4) x = 0;
   x[2] = 1;
   
   rule test;
      $display("%b", x);
      $finish(0);
   endrule
   
endmodule
