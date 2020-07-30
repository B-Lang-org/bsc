// Test the fundeps for built-in typeclass NumEq

// This proviso is OK because there is a dependency: a -> b
function Bit#(a) fn1()  provisos (NumEq#(a, b));
   return ?;
endfunction

// This proviso is OK because there is a dependency: b -> a
function Bit#(b) fn2()  provisos (NumEq#(a, b));
   return ?;
endfunction

