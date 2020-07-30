module test();
Reg#(Bit#(8)) r0<-mkReg(0);
`ifndef def1
Reg#(Bit#(8)) r1<-mkReg(0);
`ifdef def2
badcode2
`elsif def3
badcode3
`elsif def4
badcode4
`else
Reg#(Bit#(8)) r5<-mkReg(0);
`endif
Reg#(Bit#(8)) r6<-mkReg(0);
`elsif def5
badcode7
`elsif def6
badcode8
`else
badcode9
`endif
Reg#(Bit#(8)) r10<-mkReg(0);
endmodule
