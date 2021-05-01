
import Bug353_Type::*;


typedef struct {
  Bool f1;
  Bool f2;
} Foo deriving (Bits);


// -----
// Trigger error T0007

function Foo fn1();
  let res = tagged Foo {f1: True, f2: False};
  return res;
endfunction


// -----
// Trigger error T0080

function Foo fn2();
  return tagged Foo {f1: True, f2: False};
endfunction
