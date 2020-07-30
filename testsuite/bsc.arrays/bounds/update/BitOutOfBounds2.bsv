(* synthesize *)
module sysBitOutOfBounds2();
   Bit#(4) x = 0;
   x[-1] = 1;
   
   rule test;
      $display("%b", x);
      $finish(0);
   endrule
   
endmodule
