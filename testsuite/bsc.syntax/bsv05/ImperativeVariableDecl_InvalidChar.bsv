module sysImperativeVariableDecl_InvalidChar();

   Bit#(8) v1 = 0;

   // The tick is invalid here
   let v1' = v1 + 1;

   Reg#(Bit#(8)) rg <- mkReg(v1');

endmodule
