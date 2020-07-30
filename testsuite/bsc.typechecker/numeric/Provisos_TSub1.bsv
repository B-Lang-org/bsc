function Bool fn1(Bit#(n) x) provisos (Add#(TSub#(n,1), 2, k));
   return ?;
endfunction

function Bool fn(Bit#(n) x);
   return fn1(x);
endfunction

