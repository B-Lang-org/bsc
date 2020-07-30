module mkFIR3 (Reg#(data_t));

  Reg#(data_t)  acc   <- mkReg;

  rule fir_step ;
     acc <= 0;
  endrule

endmodule
