module test();
`define def5
Reg#(Bit#(8)) r0<-mkReg(0);
`ifndef def1
Reg#(Bit#(8)) r1<-mkReg(0);
`ifndef def2
Reg#(Bit#(8)) r2<-mkReg(0);
`elsif def3
badcode3
`endif
Reg#(Bit#(8)) r4<-mkReg(0);
`elsif def4
badcode5
`elsif def5
badcode6
`else
badcode7
`endif
Reg#(Bit#(8)) r8<-mkReg(0);
endmodule
