function Bool foo(Bool y);
  Bool x;
  case (y)
    True: x = !y;
//    False: x = y;
  endcase
  foo = x;
endfunction: foo

module sysImperativeFunctionCase();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(r);
  endrule
endmodule: sysImperativeFunctionCase
