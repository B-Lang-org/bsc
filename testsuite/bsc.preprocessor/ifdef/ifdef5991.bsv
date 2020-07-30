module test();
`define def1
Reg#(Bit#(8)) r0<-mkReg(0);
`ifndef def1
badcode1
`elsif def2
badcode2
`else
Reg#(Bit#(8)) r3<-mkReg(0);
`ifdef def3
badcode4
`elsif def4
badcode5
`elsif def5
badcode6
`else
Reg#(Bit#(8)) r7<-mkReg(0);
`endif
Reg#(Bit#(8)) r8<-mkReg(0);
`endif
Reg#(Bit#(8)) r9<-mkReg(0);
endmodule
