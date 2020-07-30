module mkStructUpdReg();

   Reg#(Bit#(32)) r <- mkReg(0);
   r._read = 5;
   
   rule test;
      $display(r);
   endrule

endmodule
