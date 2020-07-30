(*synthesize*)
module sysMaybeMux ();
  
  Reg#(Maybe#(int)) data         <- mkReg(Invalid);
  Reg#(Maybe#(int)) incoming     <- mkReg(Invalid);

  Reg#(Bool) b <- mkRegU;

  rule update;
    data <= b ? data : incoming ;
  endrule

endmodule

