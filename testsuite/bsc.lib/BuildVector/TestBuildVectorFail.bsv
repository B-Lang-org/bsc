import Vector::*;
import BuildVector::*;

// Test error messages

// Size too small
function Bool fn1();
  Vector#(3,Bool) v = vec(True, False, True, False);
  return (v == v);
endfunction

// Size too big
function Bool fn2();
  Vector#(3,Bool) v = vec(True, False);
  return (v == v);
endfunction

// Wrong element type, Literal
function Bool fn3();
  Vector#(3, Bool) v = vec(0, 1, 2);
  return (v == v);
endfunction

// Wrong element type, concrete
function Bool fn4();
  Vector#(3, Integer) v = vec(True, False, True);
  return (v == v);
endfunction

// Wrong return type
function Bool fn5();
  Bit#(3) v = vec(True, False, True);
  return (v == v);
endfunction

