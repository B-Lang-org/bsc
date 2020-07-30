(* synthesize *)
module sysBitOutOfBounds1();
   Bit#(4) x = 0;
   x[5] = 1;
   
   rule test;
      $display("%b", x);
      $finish(0);
   endrule
   
endmodule
