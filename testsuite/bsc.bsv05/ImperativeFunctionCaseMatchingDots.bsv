function Bool foo(Bool y);
  Bool x;
  x = True;
  case (y) matches
    True: x = False;
    False:  begin end
  endcase
  foo = x;
endfunction: foo

module sysImperativeFunctionCaseMatchingDots();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(r);
  endrule
endmodule: sysImperativeFunctionCaseMatchingDots
