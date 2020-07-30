module sysCpreprocess_unusual_format();
   Reg
#(int) i <- mkReg(190);
   rule rule1;
      $display(i);
      $finish(0);
   endrule
endmodule
