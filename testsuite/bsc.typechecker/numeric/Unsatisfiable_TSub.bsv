function Bool fn1(Bit#(n) x) provisos (Add#( TSub#(TSub#(3,n),8), 1, k));
   return ?;
endfunction

function Bool fn(Bit#(n) x);
   return fn1(x);
endfunction

