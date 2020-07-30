function Bool fn1(Bit#(n) x) provisos (Add#(TDiv#(8,n), 1, j));
   return ?;
endfunction

// This should require a proviso that "n" is not 0
function Bool fn(Bit#(n) x);
   return fn1(x);
endfunction

