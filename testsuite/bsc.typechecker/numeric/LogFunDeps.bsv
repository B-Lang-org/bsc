// Test the fundeps for built-in typeclass Log

// This proviso is OK because there is a dependency: a -> b
function Bit#(a) fn1()  provisos (Log#(a, b));
   return ?;
endfunction

// This proviso is ambiguous because there is no dependency: b -> a
function Bit#(b) fn2()  provisos (Log#(a, b));
   return ?;
endfunction

