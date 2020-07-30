function Bool fn2(Bit#(n) x) provisos (Add#(2, k, n));
   return ?;
endfunction

function Bool fn(Bit#(n) x) provisos (Add#(n, k, 1));
   return fn2(x);
endfunction

