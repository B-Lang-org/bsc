function Bool foo(bit y);
  Bool x;
  x = True;
  case (y) matches
    0: x = False;
    'b1: begin end
  endcase
  foo = x;
endfunction: foo

function Bool bar(Maybe#(bit) y);
  Bool x;
  x = True;
  case (y) matches
    tagged Invalid: x = True;
    tagged Valid (1'h0): x = False;
    tagged Valid (1): begin end
  endcase
  bar = x;
endfunction: bar

module sysImperativeFunctionCaseMatching();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(pack(r));
  endrule
endmodule: sysImperativeFunctionCaseMatching
