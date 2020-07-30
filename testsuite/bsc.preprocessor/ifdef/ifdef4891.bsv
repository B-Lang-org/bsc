module test();
`define def1
`define def3
Reg#(Bit#(8)) r0<-mkReg(0);
`ifndef def1
badcode1
`else
Reg#(Bit#(8)) r2<-mkReg(0);
`ifdef def2
badcode3
`elsif def3
Reg#(Bit#(8)) r4<-mkReg(0);
`else
badcode5
`endif
Reg#(Bit#(8)) r6<-mkReg(0);
`endif
Reg#(Bit#(8)) r7<-mkReg(0);
endmodule
