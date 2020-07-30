module test();
`define def3
`define def4
Reg#(Bit#(8)) r0<-mkReg(0);
`ifdef DEF1
badcode1
`elsif def2
badcode2
`elsif def3
Reg#(Bit#(8)) r3<-mkReg(0);
`ifdef def4
Reg#(Bit#(8)) r4<-mkReg(0);
`elsif def5
badcode5
`elsif def6
badcode6
`endif
Reg#(Bit#(8)) r7<-mkReg(0);
`endif
Reg#(Bit#(8)) r8<-mkReg(0);
endmodule
