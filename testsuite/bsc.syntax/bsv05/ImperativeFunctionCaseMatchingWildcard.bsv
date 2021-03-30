function Bool foo(Bool y);
  Bool x;
  x = True;
  case (y) matches
    True: x = False;
    .*:  x = True;
  endcase
  foo = x;
endfunction: foo

module sysImperativeFunctionCaseMatchingWildcard();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(r);
  endrule
endmodule: sysImperativeFunctionCaseMatchingWildcard
