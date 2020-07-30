function Bool fn1(Bit#(n) x) provisos (Add#(TLog#(n), 1, logn1));
   return ?;
endfunction

// This should require a proviso that "n" is not 0
function Bool fn(Bit#(n) x);
   return fn1(x);
endfunction

