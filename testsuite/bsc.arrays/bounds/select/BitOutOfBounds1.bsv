(* synthesize *)
module sysBitOutOfBounds1();
   Bit#(4) x = 4'b0101;
   Bit#(1) y = x[5];
   
   rule test;
      $display("%0b", y);
      $finish(0);
   endrule
   
endmodule
