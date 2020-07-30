// Mul#(x, 2, n) should not be necessary on "fn"

function Bit#(n) fn2(Bit#(x) v)
 provisos (Mul#(x, 2, n));

   return ?;

endfunction

function Bit#(n) fn(Bit#(x) v)
 provisos (Add#(x, x, n));

   return fn2(v);

endfunction

