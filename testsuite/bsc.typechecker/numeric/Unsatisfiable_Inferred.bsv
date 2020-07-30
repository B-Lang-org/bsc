function Bool fn1(Bit#(n) x) provisos (Add#(n, k, 1));
   return ?;
endfunction

function Bool fn2(Bit#(n) x) provisos (Add#(2, k, n));
   return ?;
endfunction

function Bool fn(Bit#(n) x);
   return (fn1(x) && fn2(x));
endfunction

