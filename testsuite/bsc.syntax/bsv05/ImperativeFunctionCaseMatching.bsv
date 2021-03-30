function Bool foo(Bool y);
  Bool x;
  x = True;
  case (y) matches
    tagged True: x = False;
    tagged False:  begin end
  endcase
  foo = x;
endfunction: foo

module sysImperativeFunctionCaseMatching();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(r);
  endrule
endmodule: sysImperativeFunctionCaseMatching
