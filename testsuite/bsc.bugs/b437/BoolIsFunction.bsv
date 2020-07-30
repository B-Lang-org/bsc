module mkFoo();
  Reg#(Maybe#(Bool)) r();
  mkReg#(True) r_inst(r);
endmodule
