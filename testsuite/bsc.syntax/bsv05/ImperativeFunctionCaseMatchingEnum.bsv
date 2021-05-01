typedef enum { MyTrue, MyFalse } MyBool;

function Bool foo(Bool y);
  Bool x;
  x = True;
  case (y) matches
    True : x = False;
    False : begin end
  endcase
  foo = x;
endfunction: foo

function Bool bar(MyBool y);
  Bool x;
  x = True;
  case (y) matches
    MyTrue : x = False;
    MyFalse: begin end
  endcase
  bar = x;
endfunction: bar

// Test enums as tagged values
function Bool baz(Maybe#(MyBool) y);
  Bool x;
  x = True;
  // Test with and without parentheses
  case (y) matches
    tagged Valid MyTrue : x = False;
    tagged Valid (MyFalse): begin end
    default: begin end
  endcase
  baz = x;
endfunction: baz

module sysImperativeFunctionCaseMatching();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    r <= foo(r);
  endrule
endmodule: sysImperativeFunctionCaseMatching
