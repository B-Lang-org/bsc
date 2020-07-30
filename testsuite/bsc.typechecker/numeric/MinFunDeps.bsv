// Test the fundeps for built-in typeclass Min

// This proviso is OK because there is a dependency: a b -> c
function Bit#(b) fn1(Bit#(a) v)  provisos (Min#(a, b, c));
   return ?;
endfunction

// This proviso is ambiguous because there is no dependency: a c -> b
function Bit#(c) fn2(Bit#(a) v)  provisos (Min#(a, b, c));
   return ?;
endfunction

// This proviso is ambiguous because there is no dependency: b c -> a
function Bit#(c) fn3(Bit#(b) v)  provisos (Min#(a, b, c));
   return ?;
endfunction

